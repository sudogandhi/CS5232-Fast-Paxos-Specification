--------------------------- MODULE FastPaxos2 -----------------------------
EXTENDS TLC, Naturals, FiniteSets, Integers

CONSTANTS Replicas
CONSTANTS None, AnyVal, Values
CONSTANTS Ballots, Quorums
CONSTANTS Coordinator, FastQuorums

VARIABLES messages
VARIABLES decision
VARIABLES maxBallot
VARIABLES maxVBallot
VARIABLES maxValue

INSTANCE Paxos

ASSUME /\ IsFiniteSet(Replicas)
       /\ Ballots \subseteq Nat
       /\ 0 \in Ballots
       /\ Any \notin Values
       /\ None \notin Values
       /\ None \notin Ballots
       /\ \A q \in Quorums : q \subseteq Replicas
       /\ \A q, r \in Quorums : q \intersect r # {}
       /\ Coordinator \in Replicas
       /\ \A q \in FastQuorums : q \subseteq Replicas
       /\ \A q, r \in FastQuorums : q \intersect r # {}
       /\ \A q \in Quorums : \A r, s \in FastQuorums : q \intersect r \intersect s # {}

FastTypeOK == PaxosTypeOK

FastInit == PaxosInit

FastNext == PaxosNext

FastSpec == /\ FastInit
            /\ [][FastNext]_<<messages, decision, maxBallot, maxVBallot, maxValue>>

===============================================================