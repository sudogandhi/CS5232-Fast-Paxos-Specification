--------------------------- MODULE Paxos -----------------------------
(*
    Notes:
    - Square brackets can be used to define a set of functions. [X -> Y]
    - Curly brackets can be used to define a set of values. {x \in SUBSET X}
*)
EXTENDS TLC, Naturals, FiniteSets, Integers

CONSTANTS Replicas
CONSTANTS None, Values
CONSTANTS Ballots

VARIABLES messages, decision

PaxosQuorums == {s \in SUBSET Replicas : (Cardinality(Replicas) \div 2) < Cardinality(s)}

P1aMessage == [type : {"P1a"},
               ballot : Ballots,
               proposer : Replicas]
P1bMessage == [type : {"P1b"},
               ballot : Ballots,
               proposer : Replicas,
               acceptor : Replicas,
               acceptBallot : Ballots,
               acceptValue : Values \union {None}]
P2aMessage == [type : {"P2a"},
               ballot : Ballots,
               proposer : Replicas,
               value : Values]
P2bMessage == [type : {"P2a"},
               ballot : Ballots,
               proposer : Replicas,
               value : Values]
Message == P1aMessage \union P1bMessage \union P2aMessage \union P2bMessage

QuorumAssume == /\ \A q \in PaxosQuorums : q \subseteq Replicas
                /\ \A q1, q2 \in PaxosQuorums : q1 \intersect q2 # {}
BallotAssume == /\ Ballots \subseteq Nat
                /\ 0 \in Ballots
ASSUME /\ QuorumAssume /\ BallotAssume

SendMessage(m) == messages' = messages \union {m}

DecideValue(r, v) == decision' = [decision EXCEPT ![r] = v]

PaxosPrepare == /\ \E b \in Ballots, r \in Replicas: SendMessage([type |-> "P1a", ballot |-> b, proposer |-> r])
                /\ UNCHANGED<<decision>>

PaxosPromise == FALSE

PaxosAccept == FALSE

PaxosAccepted == FALSE

PaxosDecide == FALSE

PaxosInit == /\ messages = {}
             /\ decision = [r \in Replicas |-> None]

PaxosNext == \/ PaxosPrepare
             \/ PaxosPromise
             \/ PaxosAccept
             \/ PaxosAccepted
             \/ PaxosDecide

PaxosTypeOK == /\ None \notin Values
               /\ messages \subseteq Message
               /\ decision \in [Replicas -> Values \union {None}]

DecideConflict == \E r1, r2 \in Replicas : /\ decision[r1] # decision[r2]
                                           /\ decision[r1] # None
                                           /\ decision[r2] # None

DecideChange == \E r \in Replicas : /\ decision[r] # decision'[r]
                                    /\ decision[r] # None
                                    /\ decision'[r] # None

PaxosSafetyProperty == [][~DecideChange]_<<messages, decision>> /\ [][~DecideConflict]_<<messages, decision>>

PaxosLivenessProperty == TRUE

PaxosSymmetry == Permutations(Values) \union Permutations(Replicas)

===============================================================