--------------------------- MODULE OrangeE2ee ---------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT
    MaxTotalUsers

\* The default (invalid) value a new user's epoch is set to
DEFAULT_EPOCH == -1
\* The value of Min({})
MIN_FAILURE == 99999999 

JoinLeaveTags == { "user_left", "user_joined" }
JoinLeaveType == [ ty: JoinLeaveTags, uid: Nat ]
MlsAddRemoveTags == { "mls_add", "mls_remove" }
MlsAddRemoveType == [ ty: MlsAddRemoveTags, epoch: Nat, target_uid: Nat, sender: Nat ]
MlsWelcomeType == [ty: {"mls_welcome"}, target_uid: Nat, epoch: Nat, sender: Nat ]
UserStateType == [
    welcomed: BOOLEAN, \* Whether this user has gotten a Welcome yet
    epoch: Nat \union {DEFAULT_EPOCH},
    idx_in_messages: Nat,
    users_pending_add: SUBSET Nat,
    users_pending_remove: SUBSET Nat
]

(* --algorithm orange
variables 
    messages = <<>>;
    \* User states are stored in order of UID
    \* Initialize with user 1
    user_states = <<[
        welcomed |-> TRUE,
        epoch |-> 0,
        idx_in_messages |-> 0,
        users_pending_add |-> <<>>,
        users_pending_remove |-> <<>>
    ]>>;
    next_free_uid = 2;
    \* Flag for when the DC is in the middle of a Welcome+Add sequence (ie might
    \* still have messages to send)
    dc_is_currently_adding = FALSE;
    \* For debugging purposes
    my_uid = 0;
    cur_branch = "";

define
    Max(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S :
        \A y \in S :
            x >= y

    Min(S) == IF S = {} THEN MIN_FAILURE ELSE CHOOSE x \in S :
        \A y \in S :
            x <= y

    TypeInvariant ==
        /\ next_free_uid \in Nat
        /\ \A j \in 1..Len(messages): \* messages consists of JoinLeave or MLS messages
            \/ messages[j] \in JoinLeaveType
            \/ messages[j] \in MlsAddRemoveType
            \/ messages[j] \in MlsWelcomeType

    \* The set of all UIDs that have joined the group
    AllUids ==  LET
        user_joined_idxs == { i \in 1..Len(messages) : messages[i]["ty"] = "user_joined" }
    IN
        { messages[i]["uid"] : i \in user_joined_idxs }
            \union {1} \* Need to add 1 because it comes by default, not via user_joined

    \* The set of UIDs which have been sent a welcome. They might not have received it yet.
    AllWelcomedUids == { uid \in AllUids :
        \E i \in 1..Len(messages) :
            /\ messages[i]["ty"] = "mls_welcome"
            /\ messages[i]["target_uid"] = uid
    } \union {1} \* User 1 is effectively welcomed, but there's no message for it

    \* The set of UIDs that have left the group
    DeadUids == { uid \in AllUids :
        \E i \in 1..Len(messages):
            /\ messages[i]["ty"] = "user_left"
            /\ messages[i]["uid"] = uid
    }


    \* The set of UIDs which have joined and not yet left
    AliveUids == AllUids \ DeadUids

    \* The set of UIDs which have joined and have been welcomed (ie are ready to participate)
    AliveWelcomedUids == AliveUids \intersect AllWelcomedUids

    \* The set of UIDs that have ever been added to the group (plus the initial member)
    AddedUids == {
        uid \in 1..Len(user_states) :
            \E j \in 1..Len(messages) :
                /\ messages[j]["ty"] = "mls_add"
                /\ messages[j]["target_uid"] = uid
    } \union {1} \* User 1 is effectively Added, but there's no message for it

    \* Given a sequence seq and an element x, returns a copy of seq without the items equal to x
    RemoveElement(seq, x) == SelectSeq(seq, LAMBDA y: x # y)

    \* Set of alive users who are not fully caught up with messages
    UsersWithUnreads == { i \in AliveUids : user_states[i]["idx_in_messages"] < Len(messages) }


    \* Set of alive users who have pending adds/removeds
    UsersWithPendings == {
        i \in AliveUids :
            \/ user_states[i]["users_pending_add"] # <<>>
            \/ user_states[i]["users_pending_remove"] # <<>>
    }

    \* Does "I am DC" have to be a local property, ie a function of idx_into_messages? Suppose two parties i < j think they're DC.
    \* Both are alive by definition. So j somehow thinks userLeft[uid=i] occurred. Contradiction. So no two parties think they are DC
    \* That said, it is possible for non-DC parties to have conflicting views on who the current DC is. But that doesn't matter.

    \* The designated committer is the smallest UID that's alive and has been Added
    DesignatedCommitter == Min(AliveUids \intersect AddedUids)

    \* The DC isn't always defined. This means the group is dead.
    DcIsDefined == DesignatedCommitter # MIN_FAILURE
    GroupIsAlive == DcIsDefined

    \* The DC doesn't always know that they're the DC. They know iff they've processed all the userLefts for the UIDs before them
    DcIsAware == IF AliveUids = {} THEN FALSE ELSE
        LET
        \* Enumerate the messages that pertain to UIDs lower than the DC leaving
        lower_uid_left == { i \in 1..Len(messages) :
            /\ messages[i]["ty"] = "user_left"
            /\ messages[i]["uid"] < DesignatedCommitter
        }
    IN
        \* Check that the DC has processed all of the requisite messages
        user_states[DesignatedCommitter]["idx_in_messages"] >= Max(lower_uid_left)

    \* The DC hasn't cleared its users_pending_add list
    DcHasPendingAdds == IF AliveWelcomedUids = {} THEN FALSE ELSE
        Len(user_states[DesignatedCommitter]["users_pending_add"]) > 0

    \* The DC hasn't cleared its users_pending_remove list
    DcHasPendingRemoves == IF AliveWelcomedUids = {} THEN FALSE ELSE
        Len(user_states[DesignatedCommitter]["users_pending_remove"]) > 0

    \* The DC has remaining elements in its users_pending_add or users_pending_remove
    DcHasPendings == DcHasPendingAdds \/ DcHasPendingRemoves

    \* Invariant: a user should never get two Adds or two Removes
    UniqueTargetUidInvariant == \A i \in 1..Len(messages) :
        messages[i]["ty"] \in MlsAddRemoveTags =>
            \A j \in 1..Len(messages):
                (j # i /\ messages[i]["ty"] = messages[j]["ty"]) =>
                    messages[i]["target_uid"] # messages[j]["target_uid"]

    \* Invariant: pendings should never have 2 of the same UID in there
    UniquePendings == \A i \in 1..Len(user_states) :
        /\ \A j,k \in 1..Len(user_states[i]["users_pending_add"]) :
              j # k => user_states[i]["users_pending_add"][j] # user_states[i]["users_pending_add"][k]
        /\ \A j,k \in 1..Len(user_states[i]["users_pending_remove"]) :
              j # k => user_states[i]["users_pending_remove"][j] # user_states[i]["users_pending_remove"][k]

    \* The epoch among Add/Remove should be monotonically increasing by 1
    MonotonicEpochInvariant ==
    LET
        all_add_removes == { i \in 1..Len(messages) : messages[i]["ty"] \in MlsAddRemoveTags }
        all_epochs == { messages[i]["epoch"] : i \in all_add_removes }
    IN
        \* Handle the trivial case
        IF all_add_removes = {} THEN TRUE ELSE
        \* Check monotonicity
        /\ \A i,j \in all_add_removes:
            i < j => messages[i]["epoch"] < messages[j]["epoch"]
        \* Check that the max epoch is the number of add/removes
        \* This and the above show that epoch is monotonically increasing by 1
        /\ Cardinality(all_add_removes) = Max(all_epochs) + 1

    \* Our simulation is done once all users have been added, every (alive) user is up to date, and
    \* the DC has no more messages to send. Either that, or the group is dead (ie the DC is undefined)
    TerminationCondition ==
        \/ ~DcIsDefined
        \/ /\ next_free_uid = MaxTotalUsers
           /\ UsersWithUnreads = {} \* Implies DcIsAware
           /\ ~DcHasPendings
           /\ ~dc_is_currently_adding


    \* Invairant:  The set of UIDs is just 1..the number of users that have been created
    UidEnumInvariant == AllUids = 1..Len(user_states)

    \* Invariant: at the end, if the group is not dead, nobody should have any pending adds/removes
    EndWithNoPendings == (TerminationCondition /\ DcIsDefined) => UsersWithPendings = {}

    \* Invariant: at the end of the simulation, every alive user has the same epoch (or the group
    \* is dead)
    EndWithEqualEpochs ==
    LET
        first_user == Min(AliveUids)
        final_epoch == user_states[first_user]["epoch"]
    IN
        \* Every alive user has the same epoch as the first alive user
        (TerminationCondition /\ GroupIsAlive) =>
            \A u \in AliveUids : user_states[u]["epoch"] = final_epoch

    \* Invariant: by the end of the simulation, every joined user received a welcome
    \* (or the group died)
    JoinImpliesWelcome == (TerminationCondition /\ GroupIsAlive) =>
        \A i \in 1..Len(messages) :
            \* Every join eventually yields a welcome
            messages[i]["ty"] = "user_joined" =>
                \E j \in 1..Len(messages) :
                    /\ j > i
                    /\ messages[j]["ty"] = "mls_welcome"
                    /\ messages[j]["target_uid"] = messages[i]["uid"]

    \* Invariant: by the end of the simulation, every welcomed user received an add
    \* (or the group died)
    WelcomeImpliesAdd == (TerminationCondition /\ GroupIsAlive) =>
        \A i \in 1..Len(messages) :
            \* Every join eventually yields a welcome
            messages[i]["ty"] = "mls_welcome" =>
                \E j \in 1..Len(messages) :
                    /\ j > i
                    /\ messages[j]["ty"] = "mls_add"
                    /\ messages[j]["target_uid"] = messages[i]["target_uid"]

end define;

\* Adds a "user_joined" event to messages. The UID is the next free UID.
\* Also adds that new user's state to the list of states. This user has not
\* been welcomed yet, but they can see join/leave messages
macro append_user_joined_event()
begin
    messages := Append(messages, [ty |-> "user_joined", uid |-> next_free_uid]);
    user_states := Append(user_states, [
        welcomed |-> FALSE,
        epoch |-> DEFAULT_EPOCH,
        idx_in_messages |-> Len(messages),
        users_pending_add |-> <<>>,
        users_pending_remove |-> <<>>
    ]);

    next_free_uid := next_free_uid + 1;
end macro;

\* Adds a "user_left" event to messages with the given UID
macro append_user_left_event(uid)
begin
    messages := Append(messages, [ty |-> "user_left", uid |-> uid]);
end macro;

\* We model the delivery service as simply removing users and adding users (up to a max)
process DeliveryService = 0
begin
    CreateJoinLeave:
        \* Loop until all users have been added
        \* TODO: users should be able to leave even after the max number of users have joined
        while next_free_uid < MaxTotalUsers do
            either
                append_user_joined_event();
            or
                with i \in AliveUids do
                    append_user_left_event(i);
                end with;
            end either;
        end while;
end process;

\* TODO: an oddity of the current process is if a user joins then leaves, it still triggers an Add
\* then Remove. Can we simplify this?

\* We model users as parties that observe and record the joins/leaves of the group, and also process
\* the welcome messages intended for just them
process Users = 1
variables
    new_msg = 0;
    new_idx = 0;
    \* Variables used for user state struct updates
    new_welcomed = 0;
    new_epoch = 0;
    new_pending_adds = 0;
    new_pending_removes = 0;
    \* Flag for whether this user was welcomed with this message
    nonwelcomed_to_welcomed = FALSE;
    \* Flag for not processing a new message (still incr'ing the idx)
    ignore_msg = FALSE;
begin
    UserMain:
        while ~TerminationCondition do
            \* Have a user with unread messages process 1 message
            with uid \in UsersWithUnreads do
                cur_branch := "Reading unreads";
                my_uid := uid;
                new_idx := user_states[uid]["idx_in_messages"] + 1;
                new_msg := messages[new_idx];

                if new_msg["ty"] \in MlsAddRemoveTags then
                    \* This is not a Welcome message, so welcomed status doesn't change
                    new_welcomed := user_states[uid]["welcomed"];
                    nonwelcomed_to_welcomed := FALSE;

                    \* Skip processing this message if some conditions are satisfied
                    if
                        \* Every Welcome is followed by an Add. If this User was just welcomed, and this is the
                        \* corresponding Add, there's no processing to do
                        \/ /\ new_msg["ty"] = "mls_add"
                           /\ new_msg["target_uid"] = uid
                           /\ new_msg["epoch"] + 1 = user_states[uid]["epoch"]
                        \* Similarly, skip processing if the DC is getting their own message
                        \/ /\ uid = DesignatedCommitter
                           \* Note: a DC's own Add/Remove could be far behind the DC's current epoch. This
                           \* happens if the DC sent many Adds/Removes before receiving any
                           /\ new_msg["epoch"] < user_states[uid]["epoch"]
                        \* Finally, ignore if not welcomed and just observing an Add/Remove for someone
                        \/    user_states[uid]["welcomed"] = FALSE

                    then
                        ignore_msg := TRUE;
                    else \* Otherwise, make sure that the Add/Remove epoch matches the user state's
                        assert user_states[uid]["epoch"] = new_msg["epoch"];
                        ignore_msg := FALSE;
                    end if; 
                else \* We always process non Add/Remove messages
                    ignore_msg := FALSE;

                    \* If this is a welcome message for us then set ourselves to welcomed and update
                    \* the epoch
                    \* Note: a user who receives 2 Welcomes will only process the first
                    if
                        /\ new_msg["ty"] = "mls_welcome"
                        /\ new_msg["target_uid"] = uid
                        /\ user_states[uid]["welcomed"] = FALSE
                    then
                        new_welcomed := TRUE;
                        nonwelcomed_to_welcomed := TRUE;
                    else
                        new_welcomed := user_states[uid]["welcomed"]; \* Unchanged
                        nonwelcomed_to_welcomed := FALSE;
                    end if;
                end if;

                \* If the message is a user join/leave, we can add to our pending adds/removes
                if new_msg["ty"] = "user_joined" /\ ~ignore_msg then
                    new_pending_adds := Append(user_states[uid]["users_pending_add"], new_msg["uid"]);
                    new_pending_removes := user_states[uid]["users_pending_remove"];
                    new_epoch := user_states[uid]["epoch"];
                elsif new_msg["ty"] = "user_left" then
                    new_pending_adds := user_states[uid]["users_pending_add"];
                    new_pending_removes := Append(user_states[uid]["users_pending_remove"], new_msg["uid"]);
                    new_epoch := user_states[uid]["epoch"];
                \* If the message is an MLS Add/Remove, we can remove from our pending adds/removes
                elsif new_msg["ty"] = "mls_add" /\ ~ignore_msg then
                    new_pending_adds:= RemoveElement(
                        user_states[uid]["users_pending_add"],
                        new_msg["target_uid"]
                    ); 
                    new_pending_removes := user_states[uid]["users_pending_remove"];
                    \* Add/Remove also increments our epoch
                    new_epoch := user_states[uid]["epoch"] + 1;
                elsif new_msg["ty"] = "mls_remove" /\ ~ignore_msg then
                    new_pending_removes := RemoveElement(
                        user_states[uid]["users_pending_remove"],
                        new_msg["target_uid"]
                    ); 
                    new_pending_adds := user_states[uid]["users_pending_add"];
                    new_epoch := user_states[uid]["epoch"] + 1;
                else
                    \* It's a Welcome or we're ignoring the message.
                    \* Either way, doesn't affect pending add/remove
                    new_pending_adds := user_states[uid]["users_pending_add"];
                    new_pending_removes := user_states[uid]["users_pending_remove"];

                    \* If we just processed a Welcome for us, then the new epoch is the given one
                    if nonwelcomed_to_welcomed then
                        new_epoch := new_msg["epoch"];
                    else \* Otherwise the epoch is unchanged
                        new_epoch := user_states[uid]["epoch"];
                    end if;
                end if;

                \* Update the user state
                user_states[uid] := [
                    welcomed |-> new_welcomed,
                    epoch |-> new_epoch,
                    idx_in_messages |-> new_idx,
                    users_pending_add |-> new_pending_adds,
                    users_pending_remove |-> new_pending_removes
                ];
            end with
        end while;
end process;

\* We model the Designated Committer, who is also a User, as doing User things above, but also
\* processing their pendings list, adding/removing others as they join/leave
process DC = 2
variables
    dc_new_idx = 0;
    \* Variables used for DC state struct updates
    dc_new_welcomed = 0;
    dc_new_epoch = 0;
    dc_new_pending_adds = 0;
    dc_new_pending_removes = 0;
    \* Used for making Adds
    dc_uid_at_start_of_add = 0;
    target_uid = 0;
begin
    DcMain:
        while ~TerminationCondition do
            await DcHasPendings /\ DcIsAware;
             \* Make the DC handle pending Adds first. Adds need to follow Welcomes always. If the
             \* last DC died, we need to start with the Adds.
            if DcHasPendingAdds then
                my_uid := DesignatedCommitter;
                dc_uid_at_start_of_add := DesignatedCommitter;
                cur_branch := "Adding pendings: Welcome";
                \* Mark that we are adding. This will be set to false once the Add is sent
                dc_is_currently_adding := TRUE;
                \* Pop the joining user from the pending list
                target_uid := Head(user_states[DesignatedCommitter]["users_pending_add"]);
                dc_new_pending_adds := Tail(user_states[DesignatedCommitter]["users_pending_add"]);
                dc_new_epoch := user_states[DesignatedCommitter]["epoch"] + 1;

                \* Update the DC state. All other vars are unchanged
                dc_new_idx := user_states[DesignatedCommitter]["idx_in_messages"];
                dc_new_welcomed := user_states[DesignatedCommitter]["welcomed"];
                dc_new_pending_removes := user_states[DesignatedCommitter]["users_pending_remove"];
                user_states[DesignatedCommitter] := [
                    welcomed |-> dc_new_welcomed,
                    epoch |-> dc_new_epoch,
                    idx_in_messages |-> dc_new_idx,
                    users_pending_add |-> dc_new_pending_adds,
                    users_pending_remove |-> dc_new_pending_removes
                ];

                \* Append a Welcome then an Add to messages
                messages := Append(messages, [
                        ty |-> "mls_welcome",
                        target_uid |-> target_uid,
                        epoch |-> dc_new_epoch,
                        sender |-> DesignatedCommitter
                ]);
              DcSendAdd: \* Label is here so that things can happen between the Welcome and Add
                \* Note: Because the DC process is different from the User process, it is possible for
                \*       the DC to send Welcome, receive the Welcome and process it, then send the Add.
                \*       The variables below are all local vars so there's no chance they're accidentally
                \*       overwritten (eg via the user_states seq) in the Users process.

                \* Do not send anything if we've died between the Welcome and Add
                if dc_uid_at_start_of_add \in DeadUids then
                    skip;
                else
                    my_uid := DesignatedCommitter;
                    cur_branch := "Adding pendings: Add";
                    messages := Append(messages, [
                            ty |-> "mls_add",
                            epoch |-> dc_new_epoch - 1,
                            target_uid |-> target_uid,
                            sender |-> dc_uid_at_start_of_add
                    ]);
                end if;

                \* We're done with the Welcome+Add op
                dc_is_currently_adding := FALSE;
            else \* DC has a pending Remove
                cur_branch := "Removing pendings";
                my_uid := DesignatedCommitter;
                \* Pop the joining user from the pending list
                target_uid := Head(user_states[DesignatedCommitter]["users_pending_remove"]);
                dc_new_pending_removes := Tail(user_states[DesignatedCommitter]["users_pending_remove"]);
                dc_new_epoch := user_states[DesignatedCommitter]["epoch"] + 1;

                \* Update the DC state. All other vars are unchanged
                dc_new_idx := user_states[DesignatedCommitter]["idx_in_messages"];
                dc_new_welcomed := user_states[DesignatedCommitter]["welcomed"];
                dc_new_pending_adds := user_states[DesignatedCommitter]["users_pending_add"];
                user_states[DesignatedCommitter] := [
                    welcomed |-> dc_new_welcomed,
                    epoch |-> dc_new_epoch,
                    idx_in_messages |-> dc_new_idx,
                    users_pending_add |-> dc_new_pending_adds,
                    users_pending_remove |-> dc_new_pending_removes
                ];

                \* Append a Remove to messages
                messages := Append(messages, [
                        ty |-> "mls_remove",
                        epoch |-> dc_new_epoch - 1,
                        target_uid |-> target_uid,
                        sender |-> DesignatedCommitter
                ]);
            end if;
        end while;
end process;
end algorithm; *)
