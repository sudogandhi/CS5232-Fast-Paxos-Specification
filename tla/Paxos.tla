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

VARIABLES messages, committed

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

CommitValue(r, v) == committed' = [committed EXCEPT ![r] = v]

PaxosPrepare == /\ \E b \in Ballots, r \in Replicas: SendMessage([type |-> "P1a", ballot |-> b, proposer |-> r])
           /\ UNCHANGED<<committed>>

PaxosPromise == FALSE

PaxosAccept == FALSE

PaxosAccepted == FALSE

PaxosCommit == FALSE

PaxosInit == /\ messages = {}
             /\ committed = [r \in Replicas |-> None]

PaxosNext == \/ PaxosPrepare
             \/ PaxosPromise
             \/ PaxosAccept
             \/ PaxosAccepted
             \/ PaxosCommit

PaxosTypeOK == /\ None \notin Values
               /\ messages \subseteq Message
               /\ committed \in [Replicas -> Values \union {None}]

CommitConflict == \E r1, r2 \in Replicas : /\ committed[r1] # committed[r2]
                                           /\ committed[r1] # None
                                           /\ committed[r2] # None

CommitChange == \E r \in Replicas : /\ committed[r] # committed'[r]
                                    /\ committed[r] # None
                                    /\ committed'[r] # None

PaxosSafetyProperty == [][~CommitChange]_<<messages, committed>> /\ [][~CommitConflict]_<<messages, committed>>

PaxosLivenessProperty == TRUE

PaxosSymmetry == Permutations(Values) \union Permutations(Replicas)

===============================================================