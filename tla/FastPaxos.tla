--------------------------- MODULE FastPaxos -----------------------------
EXTENDS TLC, Naturals, FiniteSets, Integers

CONSTANTS any, none, Replicas, Values, Ballots, Quorums
CONSTANTS FastQuorums, FastBallots

VARIABLES messages \* Set of all messages sent.
VARIABLES decision \* Decided value of an acceptor.
VARIABLES maxBallot \* Maximum ballot an acceptor has seen.
VARIABLES maxVBallot \* Maximum ballot an acceptor has accepted.
VARIABLES maxValue \* Maximum value an acceptor has accepted.
VARIABLES cValue \* Value chosen by coordinator.

INSTANCE Paxos

ClassicBallots == Ballots \ FastBallots

FastAssume == /\ \A q \in FastQuorums : q \subseteq Replicas
              /\ \A q, r \in FastQuorums : q \intersect r # {}
              /\ \A q \in Quorums : \A r, s \in FastQuorums : q \intersect r \intersect s # {}

ASSUME PaxosAssume /\ FastAssume

IsMajorityValue(M, v) == Cardinality(M) \div 2 < Cardinality({m \in M : m.value = v})

(*
    Phase 2a (Fast):

    In a fast round, the coordinator can send an P2a "any"
    message if no other values has been proposed before.
*)
FastAccept ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E f \in FastBallots :
        /\ SendMessage([type |-> "P2a",
                        ballot |-> f,
                        value |-> any])

(*
    Phase 2b (Fast):

    Acceptors can reply to a P2a "any" message with a P2b message
    containing their proposed value.
*)
FastAccepted ==
    /\ UNCHANGED<<decision, cValue>>
    /\ \E a \in Replicas, m \in p2aMessages, v \in Values:
        /\ m.value = any
        /\ maxBallot[a] <= m.ballot
        /\ maxValue[a] = none \/ maxValue[a] = v
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = v]
        /\ \A n \in p2bMessages : ~(n.ballot = m.ballot /\ n.acceptor = a)
        /\ SendMessage([type |-> "P2b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        value |-> v])

\* A value is chosen if a fast quorum of acceptors proposed that value in a fast round.
FastDecide ==
    /\ UNCHANGED<<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in FastBallots, q \in FastQuorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
            V == {w \in Values : \E m \in M : w = m.value}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ 1 = Cardinality(V)
           /\ \E m \in M : decision' = m.value

(*
    Phase 2a (Classic)

    If more than one value has been proposed, the collision is resolved using the following rules:

    1. If the votes contain different values, a value must
       be selected if the majority of acceptors in the quorum
       have casted a vote for that value.
       
    2. Otherwise, the coordinator is free to select any value.
*)
ClassicAccept ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in ClassicBallots, f \in FastBallots, q \in FastQuorums, v \in Values :
        /\ f < b \* There was a fast round before this classic round.
        /\ cValue = none \/ cValue = v
        /\ cValue' = v
        /\ \A m \in p2aMessages : m.ballot # b
        /\ LET M == {m \in p2bMessages : m.ballot = f /\ m.acceptor \in q}
               V == {w \in Values : \E m \in M : w = m.value}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ 1 < Cardinality(V) \* Collision occured.
              /\ IF \E w \in V : IsMajorityValue(M, w)
                 THEN IsMajorityValue(M, v) \* Choose majority in quorum.
                 ELSE v \in V \* Choose any.
              /\ SendMessage([type |-> "P2a",
                              ballot |-> b,
                              value |-> v])

\* Classic consensus.
ClassicDecide ==
    /\ UNCHANGED<<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in ClassicBallots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = m.value

FastTypeOK == /\ PaxosTypeOK
              /\ cValue \in Values \union {none}

FastInit == /\ PaxosInit
            /\ cValue = none

FastNext == \/ FastAccept
            \/ FastAccepted
            \/ FastDecide
            \/ ClassicAccept
            \/ PaxosAccepted /\ UNCHANGED<<cValue>>
            \/ ClassicDecide
            \/ PaxosSuccess /\ UNCHANGED<<cValue>>

FastSpec == /\ FastInit
            /\ [][FastNext]_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>
            /\ SF_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>(PaxosSuccess)

\* Only proposed values can be learnt.
FastNontriviality == \/ decision = none
                     \/ \E m \in p2bMessages : m.value = decision /\ m.ballot \in FastBallots

FastSafetyProperty == /\ [][FastNontriviality]_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>
                      /\ [][PaxosConsistency]_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>

FastSymmetry == PaxosSymmetry

===============================================================