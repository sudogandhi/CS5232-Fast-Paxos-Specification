--------------------------- MODULE FastPaxos -----------------------------
EXTENDS TLC, Naturals, FiniteSets, Integers


MaxValue(A) == CHOOSE a \in A: \A b \in A: b <= a

CONSTANT Values                 \* Set of all the values.
CONSTANT Replicas               \* Set of all replicas.
CONSTANT FastRoundNumber        \* Set of Fast Rounds.
(*
As there is only one coordinator thereofore,
Explicitly specify the name of the coordinator.
We are here also considering that the only coordinator is also the leader.
*)
CONSTANT Coordinator            

RoundNumber == Nat \ {0}        \* set of positive round numbers

ASSUME IsFiniteSet(Replicas)    \* Set of Replicas should be a Finite set.
ASSUME Coordinator \in Replicas     \* Assumption related to coordinator that it should be a member of Replicas set.
ASSUME FastRoundNumber \subseteq RoundNumber

(* It is a set of all subsets of replicas which contains count of members which is more than half of the size of set Replicas*)
FastPaxosQuorums == {q \in SUBSET Replicas : (Cardinality(Replicas) \div 2) < Cardinality(q)}
QuorumAssume == /\ \A q \in FastPaxosQuorums : q \subseteq Replicas
                /\ \A q, r \in FastPaxosQuorums : q \intersect r # {}
ASSUME QuorumAssume


(* All round numbers which are not fast rounds will be classic rounds*)
ClassicRoundRoundNumber == RoundNumber \ FastRoundNumber

\* Definition of any value and none values.
AnyValue == CHOOSE val : val \notin Values
NoneValue == CHOOSE nval : nval \notin (Values \union {AnyValue})

P1aMessage == [type : {"P1a"},
               round : RoundNumber]                       \* round is in set round.

P1bMessage == [type : {"P1b"},
               round : RoundNumber,                       \* round is in set round.
               valueRound: RoundNumber \union {0},        \* round in which value is chosen
               acceptor : Replicas,                    \* Acceptor is in set Replicas.
               value: Values \union {AnyValue}]

P2aMessage == [type : {"P2a"},
               round : RoundNumber,                       \* round value is in set round.
               value : Values]                         \* Value is in set Values.

P2bMessage == [type : {"P2b"},
               round : RoundNumber,                       \* round is in set round.
               acceptor : Replicas,                    \* Acceptor is in set Replicas.
               value : Values]                         \* Value is in set Values.

P3Message == [type : {"P3"},
              round : RoundNumber,                        \* round value is in set round.
              value : Values]                          \* Value is in set Values.

\* Message is the union of P1aMessage, P1bMessage, P2aMessage, P2bMessage and P3Message.
Message == P1aMessage \union P1bMessage \union P2aMessage \union P2bMessage \union P3Message

\* round of participation for an acceptor. 0 means has not participated in any round
VARIABLE rounds

(*
Highest numbered round in which an acceptor has casted a vote.
Initially 0.
valueRound <= round, as acceptor can participate in rounds after casting vote.
*)
VARIABLE valueRounds

(* 
Value for which an acceptor casted a vote.
*)
VARIABLE values

(*
Highest numbered round a coordinator has begun.
*)
VARIABLE coordinatorRound

(*
This value is either none, if coordinator has not picked any value,
or is equal to the value picked by the coordinator in round coordinatorRound.
*)
VARIABLE coordinatorValue
VARIABLE messages
VARIABLE proposedValue
VARIABLE learnedValue
VARIABLE goodSet

\* grouping all the variables together.
\* group of variables related to acceptor.
AcceptorVariables == <rounds,valueRounds,values>

\* group of variables related to coordinator.
CoordinatorVariables == <coordinatorRound,coordinatorValue>

\* group of all other variables
OtherVariables == <proposedValue,learnedValue,goodSet>

\* group containing all variables.
AllVarialbes == <AcceptorVariables,CoordinatorVariables,OtherVariables,messages>

\* Invariant for all the variables declared.
FastPaxosTypeOK == /\ rounds \in [Replicas -> Nat]
                   /\ valueRounds \in [Replicas -> Nat]
                   /\ values \in [Replicas -> Val \union {AnyValue}]
                   /\ coordinatorRound \in  Nat
                   /\ coordinatorValue \in Values \union {AnyValue, NoneValue}
                   /\ messages \in SUBSET Message
                   /\ proposedValue \in SUBSET  Values
                   /\ learnedValue \in SUBSET Values
                   /\ goodSet \subseteq Replicas

FastPaxosInit == /\ rounds = [Replicas |-> 0]
                 /\ valueRounds = [Replicas |-> 0]
                 /\ values = [Replicas |-> AnyValue]
                 /\ rounds = [Replicas |-> 0]
                 /\ coordinatorRound = 0
                 /\ coordinatorValue = NoneValue
                 /\ messages = {}
                 /\ proposedValue = {}
                 /\ learnedValue = {}
                 /\ goodSet \in SUBSET Replicas

SendMessage(m) == messages' = messages \union {m}

\* Implementing Phase 1a for round i
FastPaxosPrepare(i) == /\ coordinatorRound < i          \* coordinator's round number is less than the current round number i.
                       /\ \/ coordinatorRound = 0       \* if coordinator has not participated in any of the rounds yet.
                          \/ \E msg \in messages : /\ coordinatorRound < msg.round      
                                                   /\ msg.round < i
                          \/ /\ coordinatorRound \in FastRoundNumber        \* coordinator previouslt participated in a fast round.
                             /\ i \in ClassicRoundRoundNumber               \* but the current round is a classic round.
                       /\ coordinatorRound' = i
                       /\ coordinatorValue = NoneValue
                       /\ SendMessage([type |-> "P1a",round |-> i])
                       /\ UNCHANGED <AcceptorVariables,OtherVariables>

\* returns the set of all the messages for a particular phase and round and from acceptors of a particular quorum
FilterMessagesForQuorumRoundAndPhase(quorum,round,phase) == {m \in messages : (m.type = phase) /\ (m.round = round) /\ (m.acceptor \in quorum)}


===============================================================