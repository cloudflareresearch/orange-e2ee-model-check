--------------------------- MODULE orange_draft1 ---------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT MaxTotalUsers, MaxEpoch

JoinLeaveTags == { "user_left", "user_joined" }
JoinLeaveType == [ ty: JoinLeaveTags, uid: Nat ]
MlsAddRemoveTags == { "mls_add", "mls_remove" }
MlsAddRemoveType == [ ty: MlsAddRemoveTags, epoch: Nat, target_uid: Nat ]
MlsWelcomeType == [ty: {"mls_welcome"}, target_uid: Nat, epoch: Nat ]
UserStateType == [ epoch: Nat, idx_in_messages: Nat, users_pending_add: SUBSET Nat, users_pending_remove: SUBSET Nat ]

(* --algorithm orange
variables 
    messages = <<>>;
    \* This is in order of UID
    user_states = <<[
        epoch |-> 0,
        idx_in_messages |-> 0,
        users_pending_add |-> <<>>,
        users_pending_remove |-> <<>>
    ]>>;
    next_free_uid = 2;

define
    Max(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S :
        \A y \in S :
            x >= y
    
    Min(S) == IF S = {} THEN 99999999 ELSE CHOOSE x \in S :
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

    AllWelcomedUids == 1..Len(user_states)

    DeadUids == { uid \in AllUids :
        \E i \in 1..Len(messages):
            /\ messages[i]["ty"] = "user_left"
            /\ messages[i]["uid"] = uid
    }
    
    
    AliveUids == AllUids \ DeadUids
    
    AliveWelcomedUids == AliveUids \intersect AllWelcomedUids
    
    GroupIsEmpty == AllUids = DeadUids
    
    GroupIsNonempty == ~GroupIsEmpty
    
    LargestUserEpoch == Max({user_states[i]["epoch"] : i \in 1..Len(user_states)})
    
    \* Set of alive users who are not fully caught up with messages
    UsersWithUnreads == { i \in AliveWelcomedUids : user_states[i]["idx_in_messages"] < Len(messages) }
    
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

    Invariant ==
        /\ TypeInvariant
        \*/\ MaxInvariant \/ AllAreJoins
end define;

\* Adds a "user_joined" event to messages. The UID is the next free UID
macro append_user_joined_event()
begin
    messages := Append(messages, [ty |-> "user_joined", uid |-> next_free_uid]);
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
                \* Can only make a user leave if the group would not become empty
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
    new_pending_adds = 0;
    new_pending_removes = 0;
    target_uid = 0;
begin
    UserMain:
        while LargestUserEpoch < MaxEpoch do
            either \* Have a user with unread messages process 1 message
                with uid \in UsersWithUnreads do
                    new_idx := user_states[uid]["idx_in_messages"] + 1;
                    new_msg := messages[new_idx];

                    \* Can only process a message whose epoch matches
                    \* PROBLEM: DCs receive their own messages after incring their epoch, so this will fail
                    \* PROBLEM: joining users receive a Welcome with 1 epoch ahead of the Add
                    if new_msg["ty"] \in MlsAddRemoveTags then
                        assert user_states[uid]["epoch"] = new_msg["epoch"];
                    end if;

                    \* If the message is a user join/leave, we can add to our pending adds/removes
                    if new_msg["ty"] = "user_joined" then
                        new_pending_adds := user_states[uid]["users_pending_add"] \o <<new_msg["uid"]>>;
                        new_pending_removes := user_states[uid]["users_pending_remove"];
                    elsif new_msg["ty"] = "user_left" then
                        new_pending_adds := user_states[uid]["users_pending_add"];
                        new_pending_removes := user_states[uid]["users_pending_remove"] \o <<new_msg["uid"]>>;
                    \* If the message is an MLS Add/Remove, we can remove from our pending adds/removes
                    elsif new_msg["ty"] = "mls_add" then
                        \* We can just remove the head. Pendings are processed in order
                        assert Head(user_states[uid]["users_pending_add"]) = new_msg["target_uid"];
                        new_pending_adds := Tail(user_states[uid]["users_pending_add"]);
                        new_pending_removes := user_states[uid]["users_pending_remove"];
                    elsif new_msg["ty"] = "mls_remove" then
                        \* We can just remove the head. Pendings are processed in order
                        assert Head(user_states[uid]["users_pending_remove"]) = new_msg["target_uid"];
                        new_pending_adds := user_states[uid]["users_pending_add"];
                        new_pending_removes := Tail(user_states[uid]["users_pending_remove"]);
                    else
                        \* It's a Welcome. Doesn't affect pending add/remove
                        skip;
                    end if;

                    \* Update the user state
                    user_states[uid] := [
                        epoch |-> user_states[uid]["epoch"] + 1,
                        idx_in_messages |-> new_idx,
                        users_pending_add |-> new_pending_adds,
                        users_pending_remove |-> new_pending_removes
                    ];
                end with;
            or \* Make the DC send an Add if one is pending
                await DcHasPendingAdds /\ DcIsAware;
                \* Pop the joining user from the pending list
                target_uid := Head(user_states[DesignatedCommitter]["users_pending_add"]);
                user_states[DesignatedCommitter]["users_pending_add"] := Tail(user_states[DesignatedCommitter]["users_pending_add"]);
                \* Add a Welcome and an Add to messages
                messages := messages \o <<
                    [
                        ty |-> "mls_welcome",
                        target_uid |-> target_uid,
                        epoch |-> user_states[DesignatedCommitter]["epoch"] + 1
                    ],
                    [
                        ty |-> "mls_add",
                        epoch |-> user_states[DesignatedCommitter]["epoch"],
                        target_uid |-> target_uid
                    ]
                >>;
            end either;
        end while;
end process;

\* This process looks for Welcomes and appends to user_states when it sees a new one
process JoiningUsers = 2
variables
    messages_idx = 0
begin
    JoinerMain:
        while TRUE do
            \* Keep attempting to process new Welcomes
            await messages_idx < Len(messages);
            messages_idx := messages_idx + 1;
            if messages[messages_idx]["ty"] = "mls_welcome" then
                user_states := Append(user_states, [
                        epoch |-> messages[messages_idx]["epoch"],
                        idx_in_messages |-> messages_idx,
                        users_pending_add |-> {},
                        users_pending_remove |-> {}
                ]);
                assert Len(user_states) = messages[messages_idx]["target_uid"]
            end if;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "64f59e6f" /\ chksum(tla) = "cb30e3a")
VARIABLES messages, user_states, next_free_uid, pc

(* define statement *)
Max(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S :
    \A y \in S :
        x >= y

Min(S) == IF S = {} THEN 99999999 ELSE CHOOSE x \in S :
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

AllWelcomedUids == 1..Len(user_states)

DeadUids == { uid \in AllUids :
    \E i \in 1..Len(messages):
        /\ messages[i]["ty"] = "user_left"
        /\ messages[i]["uid"] = uid
}


AliveUids == AllUids \ DeadUids

AliveWelcomedUids == AliveUids \intersect AllWelcomedUids

GroupIsEmpty == AllUids = DeadUids

GroupIsNonempty == ~GroupIsEmpty

LargestUserEpoch == Max({user_states[i]["epoch"] : i \in 1..Len(user_states)})


UsersWithUnreads == { i \in AliveWelcomedUids : user_states[i]["idx_in_messages"] < Len(messages) }





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

Invariant ==
    /\ TypeInvariant

VARIABLES new_msg, new_idx, new_pending_adds, new_pending_removes, target_uid, 
          messages_idx

vars == << messages, user_states, next_free_uid, pc, new_msg, new_idx, 
           new_pending_adds, new_pending_removes, target_uid, messages_idx >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ messages = <<>>
        /\ user_states =               <<[
                             epoch |-> 0,
                             idx_in_messages |-> 0,
                             users_pending_add |-> <<>>,
                             users_pending_remove |-> <<>>
                         ]>>
        /\ next_free_uid = 2
        (* Process Users *)
        /\ new_msg = 0
        /\ new_idx = 0
        /\ new_pending_adds = 0
        /\ new_pending_removes = 0
        /\ target_uid = 0
        (* Process JoiningUsers *)
        /\ messages_idx = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "CreateJoinLeave"
                                        [] self = 1 -> "UserMain"
                                        [] self = 2 -> "JoinerMain"]

CreateJoinLeave == /\ pc[0] = "CreateJoinLeave"
                   /\ IF next_free_uid < MaxTotalUsers
                         THEN /\ \/ /\ messages' = Append(messages, [ty |-> "user_joined", uid |-> next_free_uid])
                                    /\ next_free_uid' = next_free_uid + 1
                                 \/ /\ \E i \in AliveWelcomedUids:
                                         \E j \in (AliveUids \ {i}):
                                           messages' = Append(messages, [ty |-> "user_left", uid |-> j])
                                    /\ UNCHANGED next_free_uid
                              /\ pc' = [pc EXCEPT ![0] = "CreateJoinLeave"]
                         ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                              /\ UNCHANGED << messages, next_free_uid >>
                   /\ UNCHANGED << user_states, new_msg, new_idx, 
                                   new_pending_adds, new_pending_removes, 
                                   target_uid, messages_idx >>

DeliveryService == CreateJoinLeave

UserMain == /\ pc[1] = "UserMain"
            /\ IF LargestUserEpoch < MaxEpoch
                  THEN /\ \/ /\ \E uid \in UsersWithUnreads:
                                  /\ new_idx' = user_states[uid]["idx_in_messages"] + 1
                                  /\ new_msg' = messages[new_idx']
                                  /\ IF new_msg'["ty"] \in MlsAddRemoveTags
                                        THEN /\ Assert(user_states[uid]["epoch"] = new_msg'["epoch"], 
                                                       "Failure of assertion at line 153, column 25.")
                                        ELSE /\ TRUE
                                  /\ IF new_msg'["ty"] = "user_joined"
                                        THEN /\ new_pending_adds' = user_states[uid]["users_pending_add"] \o <<new_msg'["uid"]>>
                                             /\ new_pending_removes' = user_states[uid]["users_pending_remove"]
                                        ELSE /\ IF new_msg'["ty"] = "user_left"
                                                   THEN /\ new_pending_adds' = user_states[uid]["users_pending_add"]
                                                        /\ new_pending_removes' = user_states[uid]["users_pending_remove"] \o <<new_msg'["uid"]>>
                                                   ELSE /\ IF new_msg'["ty"] = "mls_add"
                                                              THEN /\ Assert(Head(user_states[uid]["users_pending_add"]) = new_msg'["target_uid"], 
                                                                             "Failure of assertion at line 166, column 25.")
                                                                   /\ new_pending_adds' = Tail(user_states[uid]["users_pending_add"])
                                                                   /\ new_pending_removes' = user_states[uid]["users_pending_remove"]
                                                              ELSE /\ IF new_msg'["ty"] = "mls_remove"
                                                                         THEN /\ Assert(Head(user_states[uid]["users_pending_remove"]) = new_msg'["target_uid"], 
                                                                                        "Failure of assertion at line 171, column 25.")
                                                                              /\ new_pending_adds' = user_states[uid]["users_pending_add"]
                                                                              /\ new_pending_removes' = Tail(user_states[uid]["users_pending_remove"])
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED << new_pending_adds, 
                                                                                              new_pending_removes >>
                                  /\ user_states' = [user_states EXCEPT ![uid] =                     [
                                                                                     epoch |-> user_states[uid]["epoch"] + 1,
                                                                                     idx_in_messages |-> new_idx',
                                                                                     users_pending_add |-> new_pending_adds',
                                                                                     users_pending_remove |-> new_pending_removes'
                                                                                 ]]
                             /\ UNCHANGED <<messages, target_uid>>
                          \/ /\ DcHasPendingAdds /\ DcIsAware
                             /\ target_uid' = Head(user_states[DesignatedCommitter]["users_pending_add"])
                             /\ user_states' = [user_states EXCEPT ![DesignatedCommitter]["users_pending_add"] = Tail(user_states[DesignatedCommitter]["users_pending_add"])]
                             /\ messages' =             messages \o <<
                                                [
                                                    ty |-> "mls_welcome",
                                                    target_uid |-> target_uid',
                                                    epoch |-> user_states'[DesignatedCommitter]["epoch"] + 1
                                                ],
                                                [
                                                    ty |-> "mls_add",
                                                    epoch |-> user_states'[DesignatedCommitter]["epoch"],
                                                    target_uid |-> target_uid'
                                                ]
                                            >>
                             /\ UNCHANGED <<new_msg, new_idx, new_pending_adds, new_pending_removes>>
                       /\ pc' = [pc EXCEPT ![1] = "UserMain"]
                  ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                       /\ UNCHANGED << messages, user_states, new_msg, new_idx, 
                                       new_pending_adds, new_pending_removes, 
                                       target_uid >>
            /\ UNCHANGED << next_free_uid, messages_idx >>

Users == UserMain

JoinerMain == /\ pc[2] = "JoinerMain"
              /\ messages_idx < Len(messages)
              /\ messages_idx' = messages_idx + 1
              /\ IF messages[messages_idx']["ty"] = "mls_welcome"
                    THEN /\ user_states' =                Append(user_states, [
                                                   epoch |-> messages[messages_idx']["epoch"],
                                                   idx_in_messages |-> messages_idx',
                                                   users_pending_add |-> {},
                                                   users_pending_remove |-> {}
                                           ])
                         /\ Assert(Len(user_states') = messages[messages_idx']["target_uid"], 
                                   "Failure of assertion at line 226, column 17.")
                    ELSE /\ TRUE
                         /\ UNCHANGED user_states
              /\ pc' = [pc EXCEPT ![2] = "JoinerMain"]
              /\ UNCHANGED << messages, next_free_uid, new_msg, new_idx, 
                              new_pending_adds, new_pending_removes, 
                              target_uid >>

JoiningUsers == JoinerMain

Next == DeliveryService \/ Users \/ JoiningUsers

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Dec 11 02:08:26 CET 2024 by mrosenberg
\* Created Mon Dec 09 16:20:30 CET 2024 by mrosenberg
