--------------------------- MODULE orange_draft1 ---------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT MaxTotalUsers

JoinLeaveType == [ty: {"user_left", "user_joined"}, uid: Nat]
MlsMsgType == [ty: {"mls_welcome", "mls_add", "mls_remove"}, epoch: Nat]
UserStateType == [ epoch: Nat, users_pending_add: SUBSET Nat, users_pending_remove: SUBSET Nat ]

(* --algorithm orange
variables 
  messages = <<>>;
  user_states = <<>>;
  total_user_count = 1;

define
    TypeInvariant ==
        /\ total_user_count \in Nat
        /\ \A j \in 1..Len(messages): \* messages consists of JoinLeave or MLS messages
            \/ messages[j] \in JoinLeaveType
            \/ messages[j] \in MlsMsgType
    
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
    
    (*
    \* A group is empty if every user_joined has a corresponding user_left
    GroupIsEmpty == \A i \in 1..Len(messages):
        \exists j \in 1..Len(messages):
               messages[i]["uid"] = messages[j]["uid"]
            /\ messages[i]["ty"] = "user_joined"
            /\ messages[j]["ty"] = "user_left"
            
    DeadUsers == CHOOSE uid \in 1..total_user_count :
        \E i,j \in 1..Len(messages) :
            /\ i # j
            /\ messages[i]["uid"] = uid
            /\ messages[j]["uid"] = uid
            /\ messages[i]["ty"] = "user_joined"
            /\ messages[j]["ty"] = "user_left"
            
    GroupNotEmpty == \E j \in 1..Len(messages): messages[j]["ty"] = "user_joined" /\ (\A k \in 1..Len(messages) : messages[j]["uid"] = messages[k]["uid"] => j = k)
    *)
    
    
    Invariant ==
        /\ TypeInvariant
        \*/\ MaxInvariant \/ AllAreJoins
end define;

macro add_user()
begin
    messages := Append(messages, [ty |-> "user_joined", uid |-> total_user_count]);
    total_user_count := total_user_count + 1;
end macro;

macro remove_user(j)
begin
    messages := Append(messages, [ty |-> "user_left", uid |-> j]);
end macro;

process DeliveryService = 0
begin
    Main:
        while total_user_count < MaxTotalUsers do
            if GroupIsEmpty then
                add_user();
            else
                either
                    add_user();
                or
                    with j \in AliveUids do
                        remove_user(j)
                    end with;
                end either;
            end if;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "348b8a1d" /\ chksum(tla) = "9b6036fb")
VARIABLES sum, messages, total_user_count, pc

(* define statement *)
TypeInvariant ==
    /\ total_user_count \in Nat
    /\ \A j \in 1..Len(messages):
        \/ messages[j] \in JoinLeaveType
        \/ messages[j] \in MlsMsgType

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





















Invariant ==
    /\ TypeInvariant


vars == << sum, messages, total_user_count, pc >>

ProcSet == {0}

Init == (* Global variables *)
        /\ sum = 0
        /\ messages = <<>>
        /\ total_user_count = 1
        /\ pc = [self \in ProcSet |-> "Main"]

Main == /\ pc[0] = "Main"
        /\ IF total_user_count < MaxTotalUsers
              THEN /\ IF GroupIsEmpty
                         THEN /\ messages' = Append(messages, [ty |-> "user_joined", uid |-> total_user_count])
                              /\ total_user_count' = total_user_count + 1
                         ELSE /\ \/ /\ messages' = Append(messages, [ty |-> "user_joined", uid |-> total_user_count])
                                    /\ total_user_count' = total_user_count + 1
                                 \/ /\ \E j \in AliveUids:
                                         messages' = Append(messages, [ty |-> "user_left", uid |-> j])
                                    /\ UNCHANGED total_user_count
                   /\ pc' = [pc EXCEPT ![0] = "Main"]
              ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                   /\ UNCHANGED << messages, total_user_count >>
        /\ sum' = sum

DeliveryService == Main

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == DeliveryService
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Dec 09 23:32:05 CET 2024 by mrosenberg
\* Created Mon Dec 09 16:20:30 CET 2024 by mrosenberg
