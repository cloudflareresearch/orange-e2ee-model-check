--------------------------- MODULE orange_draft1 ---------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT MaxTotalUsers, NULL

JoinLeaveTags == { "user_left", "user_joined" }
JoinLeaveType == [ ty: JoinLeaveTags, uid: Nat ]
MlsAddRemoveTags == { "mls_add", "mls_remove" }
MlsAddRemoveType == [ ty: MlsAddRemoveTags, epoch: Nat, target_uid: Nat, sender: Nat ]
MlsWelcomeType == [ty: {"mls_welcome"}, target_uid: Nat, epoch: Nat, sender: Nat ]
UserStateType == [
    welcomed: BOOLEAN, \* Whether this user has gotten a Welcome yet
    epoch: Nat \union {NULL},
    idx_in_messages: Nat,
    users_pending_add: SUBSET Nat,
    users_pending_remove: SUBSET Nat
]

(* --algorithm orange
variables 
    messages = <<>>;
    \* This is in order of UID
    user_states = <<[
        welcomed |-> TRUE,
        epoch |-> 0,
        idx_in_messages |-> 0,
        users_pending_add |-> <<>>,
        users_pending_remove |-> <<>>
    ]>>;
    next_free_uid = 2;
    \* For debugging purposes
    my_uid = 0;
    cur_branch = "";

define
    Max(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S :
        \A y \in S :
            x >= y
    
    Min(S) == IF S = {} THEN Assert(FALSE, "min of empty set") ELSE CHOOSE x \in S :
        \A y \in S :
            x <= y

    TypeInvariant ==
        /\ next_free_uid \in Nat
        /\ \A j \in 1..Len(messages): \* messages consists of JoinLeave or MLS messages
            \/ messages[j] \in JoinLeaveType
            \/ messages[j] \in MlsAddRemoveType
            \/ messages[j] \in MlsWelcomeType
    
    AllAreJoins == \A j \in 1..Len(messages): messages[j]["ty"] = "user_joined"
    
    MaxInvariant == \A j \in 1..Len(messages): messages[j]["uid"] < 6
    
    AllUids ==  LET
        user_joined_idxs == { i \in 1..Len(messages) : messages[i]["ty"] = "user_joined" }
    IN
        { messages[i]["uid"] : i \in user_joined_idxs }
            \union {1} \* Need to add 1 because it comes by default, not via user_joined

    \* The set of UIDs which have been sent a welcome. They might not have received it yet.
    \* TODO: Rename this to something like "users that are able or will be able to participate"
    AllWelcomedUids == { uid \in AllUids :
        \E i \in 1..Len(messages) :
            /\ messages[i]["ty"] = "mls_welcome"
            /\ messages[i]["target_uid"] = uid
    } \union {1} \* User 1 is effectively welcomed, but there's no message for it

    DeadUids == { uid \in AllUids :
        \E i \in 1..Len(messages):
            /\ messages[i]["ty"] = "user_left"
            /\ messages[i]["uid"] = uid
    }
    
    
    AliveUids == AllUids \ DeadUids
    
    AliveWelcomedUids == AliveUids \intersect AllWelcomedUids
    
    AliveNonwelcomedUids == AliveUids \ AllWelcomedUids
    
    GroupIsEmpty == AllUids = DeadUids
    
    GroupIsNonempty == ~GroupIsEmpty
    
    LargestUserEpoch == Max({user_states[i]["epoch"] : i \in 1..Len(user_states)})

    \* Given a sequence seq and an element x, returns a copy of seq without the items equal to x
    RemoveElement(seq, x) == SelectSeq(seq, LAMBDA y: x # y)
    
    \* Set of alive users who are not fully caught up with messages
    UsersWithUnreads == { i \in AliveUids : user_states[i]["idx_in_messages"] < Len(messages) }

    \* Set of alive, nonwelcomed users who are not fully caught up with messages
    NonwelcomedUsersWithUnreads == { i \in AliveNonwelcomedUids : user_states[i]["idx_in_messages"] < Len(messages) }
    
    \* Does "I am DC" have to be a local property, ie a function of idx_into_messages? Suppose two parties i < j think they're DC.
    \* Both are alive by definition. So j somehow thinks userLeft[uid=i] occurred. Contradiction. So no two parties think they are DC
    \* That said, it is possible for non-DC parties to have conflicting views on who the current DC is. But that doesn't matter.

    DesignatedCommitter == Min(AliveUids)
    
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

    DcHasPendingAdds == IF AliveWelcomedUids = {} THEN FALSE ELSE
        Len(user_states[DesignatedCommitter]["users_pending_add"]) > 0

    DcHasPendingRemoves == IF AliveWelcomedUids = {} THEN FALSE ELSE
        Len(user_states[DesignatedCommitter]["users_pending_remove"]) > 0
        
    \* The complex way of creating UIDs should be the same as the easy way
    UidEnumInvariant == AllUids = 1..Len(user_states)
    
    \* If the leftmost alvie UID is not welcomed, then the group is stuck. We make sure this is
    \* impossible in our setup
    DcInvariant == Min(AliveUids) = Min(AliveWelcomedUids)

end define;

\* Invariant: a joined user must always receive a welcome.
\*     more specifically: no add/remove messages can happen until a Welcome happens
\* Invariant: the DC is always welcomed

\* Invariant: Every welcomed user is eventually added

\* Invariant: users who have been added do not appear on the users_pending_add lists of up-to-date users

\* Invariant: pendings should never have 2 of the same item in there

\* Invariant: added/removed users should eventually make it off pending lists

\* A DC should never receive an epoch ahead of its current epoch

\* Adds a "user_joined" event to messages. The UID is the next free UID.
\* Also adds that new user's state to the list of states. This user has not
\* been welcomed yet, but they can see join/leave messages
macro append_user_joined_event()
begin
    messages := Append(messages, [ty |-> "user_joined", uid |-> next_free_uid]);
    user_states := Append(user_states, [
        welcomed |-> FALSE,
        epoch |-> NULL,
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

process DeliveryService = 0
begin
    CreateJoinLeave:
        while next_free_uid < MaxTotalUsers do
            either
                append_user_joined_event();
            or
                \* TODO: Remove this condition. Allow the model to terminate if every user leaves
                \* To avoid deadlock, we only make a user leave if the group would not become empty
                with i \in AliveWelcomedUids do
                    with j \in (AliveUids \ {i}) do
                        append_user_left_event(j);
                    end with;
                end with;
            end either;
        end while;
end process;

\* ODDITY: if a user joins then leaves, it still triggers an Add then Remove. Can we simplify this?

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
        \* Loop until all users have been added and everyone is up to date
        while next_free_uid < MaxTotalUsers \/ UsersWithUnreads # {} do
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
                        \* Similarly, skip processing is the DC getting their own message
                        \/ /\ uid = DesignatedCommitter
                           \* Note: a DC's own Add/Remove could be far behind the DC's current epoch. This
                           \* happens if the DC sent many Adds/Removes before receiving any
                           /\ new_msg["epoch"] # user_states[uid]["epoch"]
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
        while next_free_uid < MaxTotalUsers \/ UsersWithUnreads # {} do
            either \* Make the DC send an Add if one is pending
                await DcHasPendingAdds /\ DcIsAware;
                my_uid := DesignatedCommitter;
                dc_uid_at_start_of_add := DesignatedCommitter;
                cur_branch := "Adding pendings: Welcome";
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
                
                \* Do not send anything if we've been removed between the Welcome and Add
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
            or \* Make the DC send a Remove if one is pending
                await DcHasPendingRemoves /\ DcIsAware;
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
            end either;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f2863549" /\ chksum(tla) = "57156f05")
VARIABLES messages, user_states, next_free_uid, my_uid, cur_branch, pc

(* define statement *)
Max(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S :
    \A y \in S :
        x >= y

Min(S) == IF S = {} THEN Assert(FALSE, "min of empty set") ELSE CHOOSE x \in S :
    \A y \in S :
        x <= y

TypeInvariant ==
    /\ next_free_uid \in Nat
    /\ \A j \in 1..Len(messages):
        \/ messages[j] \in JoinLeaveType
        \/ messages[j] \in MlsAddRemoveType
        \/ messages[j] \in MlsWelcomeType

AllAreJoins == \A j \in 1..Len(messages): messages[j]["ty"] = "user_joined"

MaxInvariant == \A j \in 1..Len(messages): messages[j]["uid"] < 6

AllUids ==  LET
    user_joined_idxs == { i \in 1..Len(messages) : messages[i]["ty"] = "user_joined" }
IN
    { messages[i]["uid"] : i \in user_joined_idxs }
        \union {1}



AllWelcomedUids == { uid \in AllUids :
    \E i \in 1..Len(messages) :
        /\ messages[i]["ty"] = "mls_welcome"
        /\ messages[i]["target_uid"] = uid
} \union {1}

DeadUids == { uid \in AllUids :
    \E i \in 1..Len(messages):
        /\ messages[i]["ty"] = "user_left"
        /\ messages[i]["uid"] = uid
}


AliveUids == AllUids \ DeadUids

AliveWelcomedUids == AliveUids \intersect AllWelcomedUids

AliveNonwelcomedUids == AliveUids \ AllWelcomedUids

GroupIsEmpty == AllUids = DeadUids

GroupIsNonempty == ~GroupIsEmpty

LargestUserEpoch == Max({user_states[i]["epoch"] : i \in 1..Len(user_states)})


RemoveElement(seq, x) == SelectSeq(seq, LAMBDA y: x # y)


UsersWithUnreads == { i \in AliveUids : user_states[i]["idx_in_messages"] < Len(messages) }


NonwelcomedUsersWithUnreads == { i \in AliveNonwelcomedUids : user_states[i]["idx_in_messages"] < Len(messages) }





DesignatedCommitter == Min(AliveUids)


DcIsAware == IF AliveUids = {} THEN FALSE ELSE
    LET

    lower_uid_left == { i \in 1..Len(messages) :
        /\ messages[i]["ty"] = "user_left"
        /\ messages[i]["uid"] < DesignatedCommitter
    }
IN

    user_states[DesignatedCommitter]["idx_in_messages"] >= Max(lower_uid_left)

DcHasPendingAdds == IF AliveWelcomedUids = {} THEN FALSE ELSE
    Len(user_states[DesignatedCommitter]["users_pending_add"]) > 0

DcHasPendingRemoves == IF AliveWelcomedUids = {} THEN FALSE ELSE
    Len(user_states[DesignatedCommitter]["users_pending_remove"]) > 0


UidEnumInvariant == AllUids = 1..Len(user_states)



DcInvariant == Min(AliveUids) = Min(AliveWelcomedUids)

VARIABLES new_msg, new_idx, new_welcomed, new_epoch, new_pending_adds, 
          new_pending_removes, nonwelcomed_to_welcomed, ignore_msg, 
          dc_new_idx, dc_new_welcomed, dc_new_epoch, dc_new_pending_adds, 
          dc_new_pending_removes, dc_uid_at_start_of_add, target_uid

vars == << messages, user_states, next_free_uid, my_uid, cur_branch, pc, 
           new_msg, new_idx, new_welcomed, new_epoch, new_pending_adds, 
           new_pending_removes, nonwelcomed_to_welcomed, ignore_msg, 
           dc_new_idx, dc_new_welcomed, dc_new_epoch, dc_new_pending_adds, 
           dc_new_pending_removes, dc_uid_at_start_of_add, target_uid >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ messages = <<>>
        /\ user_states =               <<[
                             welcomed |-> TRUE,
                             epoch |-> 0,
                             idx_in_messages |-> 0,
                             users_pending_add |-> <<>>,
                             users_pending_remove |-> <<>>
                         ]>>
        /\ next_free_uid = 2
        /\ my_uid = 0
        /\ cur_branch = ""
        (* Process Users *)
        /\ new_msg = 0
        /\ new_idx = 0
        /\ new_welcomed = 0
        /\ new_epoch = 0
        /\ new_pending_adds = 0
        /\ new_pending_removes = 0
        /\ nonwelcomed_to_welcomed = FALSE
        /\ ignore_msg = FALSE
        (* Process DC *)
        /\ dc_new_idx = 0
        /\ dc_new_welcomed = 0
        /\ dc_new_epoch = 0
        /\ dc_new_pending_adds = 0
        /\ dc_new_pending_removes = 0
        /\ dc_uid_at_start_of_add = 0
        /\ target_uid = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "CreateJoinLeave"
                                        [] self = 1 -> "UserMain"
                                        [] self = 2 -> "DcMain"]

CreateJoinLeave == /\ pc[0] = "CreateJoinLeave"
                   /\ IF next_free_uid < MaxTotalUsers
                         THEN /\ \/ /\ messages' = Append(messages, [ty |-> "user_joined", uid |-> next_free_uid])
                                    /\ user_states' =                Append(user_states, [
                                                          welcomed |-> FALSE,
                                                          epoch |-> NULL,
                                                          idx_in_messages |-> Len(messages'),
                                                          users_pending_add |-> <<>>,
                                                          users_pending_remove |-> <<>>
                                                      ])
                                    /\ next_free_uid' = next_free_uid + 1
                                 \/ /\ \E i \in AliveWelcomedUids:
                                         \E j \in (AliveUids \ {i}):
                                           messages' = Append(messages, [ty |-> "user_left", uid |-> j])
                                    /\ UNCHANGED <<user_states, next_free_uid>>
                              /\ pc' = [pc EXCEPT ![0] = "CreateJoinLeave"]
                         ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                              /\ UNCHANGED << messages, user_states, 
                                              next_free_uid >>
                   /\ UNCHANGED << my_uid, cur_branch, new_msg, new_idx, 
                                   new_welcomed, new_epoch, new_pending_adds, 
                                   new_pending_removes, 
                                   nonwelcomed_to_welcomed, ignore_msg, 
                                   dc_new_idx, dc_new_welcomed, dc_new_epoch, 
                                   dc_new_pending_adds, dc_new_pending_removes, 
                                   dc_uid_at_start_of_add, target_uid >>

DeliveryService == CreateJoinLeave

UserMain == /\ pc[1] = "UserMain"
            /\ IF next_free_uid < MaxTotalUsers \/ UsersWithUnreads # {}
                  THEN /\ \E uid \in UsersWithUnreads:
                            /\ cur_branch' = "Reading unreads"
                            /\ my_uid' = uid
                            /\ new_idx' = user_states[uid]["idx_in_messages"] + 1
                            /\ new_msg' = messages[new_idx']
                            /\ IF new_msg'["ty"] \in MlsAddRemoveTags
                                  THEN /\ new_welcomed' = user_states[uid]["welcomed"]
                                       /\ nonwelcomed_to_welcomed' = FALSE
                                       /\ IF \/ /\ new_msg'["ty"] = "mls_add"
                                                /\ new_msg'["target_uid"] = uid
                                                /\ new_msg'["epoch"] + 1 = user_states[uid]["epoch"]
                                             
                                             \/ /\ uid = DesignatedCommitter
                                             
                                             
                                                /\ new_msg'["epoch"] # user_states[uid]["epoch"]
                                             
                                             \/    user_states[uid]["welcomed"] = FALSE
                                             THEN /\ ignore_msg' = TRUE
                                             ELSE /\ Assert(user_states[uid]["epoch"] = new_msg'["epoch"], 
                                                            "Failure of assertion at line 234, column 25.")
                                                  /\ ignore_msg' = FALSE
                                  ELSE /\ ignore_msg' = FALSE
                                       /\ IF /\ new_msg'["ty"] = "mls_welcome"
                                             /\ new_msg'["target_uid"] = uid
                                             /\ user_states[uid]["welcomed"] = FALSE
                                             THEN /\ new_welcomed' = TRUE
                                                  /\ nonwelcomed_to_welcomed' = TRUE
                                             ELSE /\ new_welcomed' = user_states[uid]["welcomed"]
                                                  /\ nonwelcomed_to_welcomed' = FALSE
                            /\ IF new_msg'["ty"] = "user_joined" /\ ~ignore_msg'
                                  THEN /\ new_pending_adds' = Append(user_states[uid]["users_pending_add"], new_msg'["uid"])
                                       /\ new_pending_removes' = user_states[uid]["users_pending_remove"]
                                       /\ new_epoch' = user_states[uid]["epoch"]
                                  ELSE /\ IF new_msg'["ty"] = "user_left"
                                             THEN /\ new_pending_adds' = user_states[uid]["users_pending_add"]
                                                  /\ new_pending_removes' = Append(user_states[uid]["users_pending_remove"], new_msg'["uid"])
                                                  /\ new_epoch' = user_states[uid]["epoch"]
                                             ELSE /\ IF new_msg'["ty"] = "mls_add" /\ ~ignore_msg'
                                                        THEN /\ new_pending_adds' =                    RemoveElement(
                                                                                        user_states[uid]["users_pending_add"],
                                                                                        new_msg'["target_uid"]
                                                                                    )
                                                             /\ new_pending_removes' = user_states[uid]["users_pending_remove"]
                                                             /\ new_epoch' = user_states[uid]["epoch"] + 1
                                                        ELSE /\ IF new_msg'["ty"] = "mls_remove" /\ ~ignore_msg'
                                                                   THEN /\ new_pending_removes' =                        RemoveElement(
                                                                                                      user_states[uid]["users_pending_remove"],
                                                                                                      new_msg'["target_uid"]
                                                                                                  )
                                                                        /\ new_pending_adds' = user_states[uid]["users_pending_add"]
                                                                        /\ new_epoch' = user_states[uid]["epoch"] + 1
                                                                   ELSE /\ new_pending_adds' = user_states[uid]["users_pending_add"]
                                                                        /\ new_pending_removes' = user_states[uid]["users_pending_remove"]
                                                                        /\ IF nonwelcomed_to_welcomed'
                                                                              THEN /\ new_epoch' = new_msg'["epoch"]
                                                                              ELSE /\ new_epoch' = user_states[uid]["epoch"]
                            /\ user_states' = [user_states EXCEPT ![uid] =                     [
                                                                               welcomed |-> new_welcomed',
                                                                               epoch |-> new_epoch',
                                                                               idx_in_messages |-> new_idx',
                                                                               users_pending_add |-> new_pending_adds',
                                                                               users_pending_remove |-> new_pending_removes'
                                                                           ]]
                       /\ pc' = [pc EXCEPT ![1] = "UserMain"]
                  ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                       /\ UNCHANGED << user_states, my_uid, cur_branch, 
                                       new_msg, new_idx, new_welcomed, 
                                       new_epoch, new_pending_adds, 
                                       new_pending_removes, 
                                       nonwelcomed_to_welcomed, ignore_msg >>
            /\ UNCHANGED << messages, next_free_uid, dc_new_idx, 
                            dc_new_welcomed, dc_new_epoch, dc_new_pending_adds, 
                            dc_new_pending_removes, dc_uid_at_start_of_add, 
                            target_uid >>

Users == UserMain

DcMain == /\ pc[2] = "DcMain"
          /\ IF next_free_uid < MaxTotalUsers \/ UsersWithUnreads # {}
                THEN /\ \/ /\ DcHasPendingAdds /\ DcIsAware
                           /\ my_uid' = DesignatedCommitter
                           /\ dc_uid_at_start_of_add' = DesignatedCommitter
                           /\ cur_branch' = "Adding pendings: Welcome"
                           /\ target_uid' = Head(user_states[DesignatedCommitter]["users_pending_add"])
                           /\ dc_new_pending_adds' = Tail(user_states[DesignatedCommitter]["users_pending_add"])
                           /\ dc_new_epoch' = user_states[DesignatedCommitter]["epoch"] + 1
                           /\ dc_new_idx' = user_states[DesignatedCommitter]["idx_in_messages"]
                           /\ dc_new_welcomed' = user_states[DesignatedCommitter]["welcomed"]
                           /\ dc_new_pending_removes' = user_states[DesignatedCommitter]["users_pending_remove"]
                           /\ user_states' = [user_states EXCEPT ![DesignatedCommitter] =                                     [
                                                                                              welcomed |-> dc_new_welcomed',
                                                                                              epoch |-> dc_new_epoch',
                                                                                              idx_in_messages |-> dc_new_idx',
                                                                                              users_pending_add |-> dc_new_pending_adds',
                                                                                              users_pending_remove |-> dc_new_pending_removes'
                                                                                          ]]
                           /\ messages' =             Append(messages, [
                                                  ty |-> "mls_welcome",
                                                  target_uid |-> target_uid',
                                                  epoch |-> dc_new_epoch',
                                                  sender |-> DesignatedCommitter
                                          ])
                           /\ pc' = [pc EXCEPT ![2] = "DcSendAdd"]
                        \/ /\ DcHasPendingRemoves /\ DcIsAware
                           /\ cur_branch' = "Removing pendings"
                           /\ my_uid' = DesignatedCommitter
                           /\ target_uid' = Head(user_states[DesignatedCommitter]["users_pending_remove"])
                           /\ dc_new_pending_removes' = Tail(user_states[DesignatedCommitter]["users_pending_remove"])
                           /\ dc_new_epoch' = user_states[DesignatedCommitter]["epoch"] + 1
                           /\ dc_new_idx' = user_states[DesignatedCommitter]["idx_in_messages"]
                           /\ dc_new_welcomed' = user_states[DesignatedCommitter]["welcomed"]
                           /\ dc_new_pending_adds' = user_states[DesignatedCommitter]["users_pending_add"]
                           /\ user_states' = [user_states EXCEPT ![DesignatedCommitter] =                                     [
                                                                                              welcomed |-> dc_new_welcomed',
                                                                                              epoch |-> dc_new_epoch',
                                                                                              idx_in_messages |-> dc_new_idx',
                                                                                              users_pending_add |-> dc_new_pending_adds',
                                                                                              users_pending_remove |-> dc_new_pending_removes'
                                                                                          ]]
                           /\ messages' =             Append(messages, [
                                                  ty |-> "mls_remove",
                                                  epoch |-> dc_new_epoch' - 1,
                                                  target_uid |-> target_uid',
                                                  sender |-> DesignatedCommitter
                                          ])
                           /\ pc' = [pc EXCEPT ![2] = "DcMain"]
                           /\ UNCHANGED dc_uid_at_start_of_add
                ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
                     /\ UNCHANGED << messages, user_states, my_uid, cur_branch, 
                                     dc_new_idx, dc_new_welcomed, dc_new_epoch, 
                                     dc_new_pending_adds, 
                                     dc_new_pending_removes, 
                                     dc_uid_at_start_of_add, target_uid >>
          /\ UNCHANGED << next_free_uid, new_msg, new_idx, new_welcomed, 
                          new_epoch, new_pending_adds, new_pending_removes, 
                          nonwelcomed_to_welcomed, ignore_msg >>

DcSendAdd == /\ pc[2] = "DcSendAdd"
             /\ IF dc_uid_at_start_of_add \in DeadUids
                   THEN /\ TRUE
                        /\ UNCHANGED << messages, my_uid, cur_branch >>
                   ELSE /\ my_uid' = DesignatedCommitter
                        /\ cur_branch' = "Adding pendings: Add"
                        /\ messages' =             Append(messages, [
                                               ty |-> "mls_add",
                                               epoch |-> dc_new_epoch - 1,
                                               target_uid |-> target_uid,
                                               sender |-> dc_uid_at_start_of_add
                                       ])
             /\ pc' = [pc EXCEPT ![2] = "DcMain"]
             /\ UNCHANGED << user_states, next_free_uid, new_msg, new_idx, 
                             new_welcomed, new_epoch, new_pending_adds, 
                             new_pending_removes, nonwelcomed_to_welcomed, 
                             ignore_msg, dc_new_idx, dc_new_welcomed, 
                             dc_new_epoch, dc_new_pending_adds, 
                             dc_new_pending_removes, dc_uid_at_start_of_add, 
                             target_uid >>

DC == DcMain \/ DcSendAdd

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == DeliveryService \/ Users \/ DC
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Dec 17 00:14:55 CET 2024 by mrosenberg
\* Created Mon Dec 09 16:20:30 CET 2024 by mrosenberg
