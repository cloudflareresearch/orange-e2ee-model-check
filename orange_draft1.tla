--------------------------- MODULE orange_draft1 ---------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT MaxTotalUsers, MaxEpoch

JoinLeaveTags == { "user_left", "user_joined" }
JoinLeaveType == [ ty: JoinLeaveTags, uid: Nat ]
MlsAddRemoveTags == { "mls_add", "mls_remove" }
MlsAddRemoveType == [ ty: MlsAddRemoveTags, epoch: Nat ]
MlsWelcomeType == [ty: {"mls_welcome"}, uid: Nat, epoch: Nat ]
UserStateType == [ epoch: Nat, idx_in_messages: Nat, users_pending_add: SUBSET Nat, users_pending_remove: SUBSET Nat ]

(* --algorithm orange
variables 
  messages = <<>>;
  user_states = <<>>; \* This is in order of UID
  next_free_uid = 1;

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

    DeadUids == { uid \in AllUids :
        \E i,j \in 1..Len(messages):
            /\ i # j
            /\ messages[i]["ty"] = "user_joined"
            /\ messages[j]["ty"] = "user_left"
            /\ messages[i]["uid"] = uid
            /\ messages[j]["uid"] = uid
    }
    
    AliveUids == AllUids \ DeadUids
    
    GroupIsEmpty == AllUids = DeadUids
    
    GroupIsNonempty == ~GroupIsEmpty
    
    LargestUserEpoch == Max({user_states[i]["epoch"] : i \in 1..Len(user_states)})
    
    \* Set of alive users who are not fully caught up with messages
    UsersWithUnreads == { i \in AliveUids : user_states[i]["idx_in_messages"] < Len(messages) }
    
    \* Does "I am DC" have to be a local property, ie a function of idx_into_messages? Suppose two parties i < j think they're DC.
    \* Both are alive by definition. So j somehow thinks userLeft[uid=i] occurred. Contradiction. So no two parties think they are DC
    \* That said, it is possible for non-DC parties to have conflicting views on who the current DC is. But that doesn't matter.

    DesignatedCommitter == Min(AliveUids)
    
    \* The DC doesn't always know that they're the DC. They know iff they've processed all the userLefts for the UIDs before them
    DcIsReady == IF AliveUids = {} THEN FALSE ELSE
        LET
        \* Enumerate the messages that pertain to UIDs lower than the DC leaving
        lower_uid_left == { i \in Len(messages) :
            /\ messages[i]["ty"] = "userLeft"
            /\ messages[i]["uid"] < DesignatedCommitter
        }
    IN
        \* Check that the DC has processed all of the requisite messages
        user_states[DesignatedCommitter]["idx_in_messages"] >= Max(lower_uid_left)  

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
    Main:
        while next_free_uid < MaxTotalUsers do
            either
                append_user_joined_event();
            or
                await GroupIsNonempty; \* Can only Remove if the group is nonempty
                with j \in AliveUids do
                    append_user_left_event(j);
                end with;
            end either;
        end while;
end process;

process Users = 1
begin
    UserMain:
        while LargestUserEpoch < MaxEpoch do
            with uid \in AliveUids do
                skip;
            end with;
            skip;
        end while;
end process;

\* This process looks for Welcomes and appends to user_states when it sees a new one
process JoiningUsers = 2
variables
    messages_idx = 0
begin
    JoningMain:
        while TRUE do
            \* Keep attempting to process new Welcomes
            if messages_idx < Len(messages) then
                messages_idx := messages_idx + 1;
                if messages[messages_idx]["ty"] = "mls_welcome" then
                    user_states := Append(user_states, [
                            epoch |-> messages[messages_idx]["epoch"],
                            idx_in_messages |-> messages_idx,
                            users_pending_add |-> {},
                            users_pending_remove |-> {}
                    ]);
                    assert Len(user_states) = messages[messages_idx]["epoch"]
                end if;
            end if;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b205f398" /\ chksum(tla) = "8d47e001")
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

DeadUids == { uid \in AllUids :
    \E i,j \in 1..Len(messages):
        /\ i # j
        /\ messages[i]["ty"] = "user_joined"
        /\ messages[j]["ty"] = "user_left"
        /\ messages[i]["uid"] = uid
        /\ messages[j]["uid"] = uid
}

AliveUids == AllUids \ DeadUids

GroupIsEmpty == AllUids = DeadUids

GroupIsNonempty == ~GroupIsEmpty

LargestUserEpoch == Max({user_states[i]["epoch"] : i \in 1..Len(user_states)})


UsersWithUnreads == { i \in AliveUids : user_states[i]["idx_in_messages"] < Len(messages) }





DesignatedCommitter == Min(AliveUids)


DcIsReady == IF AliveUids = {} THEN FALSE ELSE
    LET

    lower_uid_left == { i \in Len(messages) :
        /\ messages[i]["ty"] = "userLeft"
        /\ messages[i]["uid"] < DesignatedCommitter
    }
IN

    user_states[DesignatedCommitter]["idx_in_messages"] >= Max(lower_uid_left)

Invariant ==
    /\ TypeInvariant

VARIABLE messages_idx

vars == << messages, user_states, next_free_uid, pc, messages_idx >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ messages = <<>>
        /\ user_states = <<>>
        /\ next_free_uid = 1
        (* Process JoiningUsers *)
        /\ messages_idx = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "Main"
                                        [] self = 1 -> "UserMain"
                                        [] self = 2 -> "JoningMain"]

Main == /\ pc[0] = "Main"
        /\ IF next_free_uid < MaxTotalUsers
              THEN /\ \/ /\ messages' = Append(messages, [ty |-> "user_joined", uid |-> next_free_uid])
                         /\ next_free_uid' = next_free_uid + 1
                      \/ /\ GroupIsNonempty
                         /\ \E j \in AliveUids:
                              messages' = Append(messages, [ty |-> "user_left", uid |-> j])
                         /\ UNCHANGED next_free_uid
                   /\ pc' = [pc EXCEPT ![0] = "Main"]
              ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                   /\ UNCHANGED << messages, next_free_uid >>
        /\ UNCHANGED << user_states, messages_idx >>

DeliveryService == Main

UserMain == /\ pc[1] = "UserMain"
            /\ IF LargestUserEpoch < MaxEpoch
                  THEN /\ \E uid \in AliveUids:
                            TRUE
                       /\ TRUE
                       /\ pc' = [pc EXCEPT ![1] = "UserMain"]
                  ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
            /\ UNCHANGED << messages, user_states, next_free_uid, messages_idx >>

Users == UserMain

JoningMain == /\ pc[2] = "JoningMain"
              /\ IF messages_idx < Len(messages)
                    THEN /\ messages_idx' = messages_idx + 1
                         /\ IF messages[messages_idx']["ty"] = "mls_welcome"
                               THEN /\ user_states' =                Append(user_states, [
                                                              epoch |-> messages[messages_idx']["epoch"],
                                                              idx_in_messages |-> messages_idx',
                                                              users_pending_add |-> {},
                                                              users_pending_remove |-> {}
                                                      ])
                                    /\ Assert(Len(user_states') = messages[messages_idx']["epoch"], 
                                              "Failure of assertion at line 143, column 21.")
                               ELSE /\ TRUE
                                    /\ UNCHANGED user_states
                    ELSE /\ TRUE
                         /\ UNCHANGED << user_states, messages_idx >>
              /\ pc' = [pc EXCEPT ![2] = "JoningMain"]
              /\ UNCHANGED << messages, next_free_uid >>

JoiningUsers == JoningMain

Next == DeliveryService \/ Users \/ JoiningUsers

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Dec 10 17:01:27 CET 2024 by mrosenberg
\* Created Mon Dec 09 16:20:30 CET 2024 by mrosenberg
