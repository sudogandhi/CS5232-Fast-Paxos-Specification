--------------------------- MODULE FastPaxos -----------------------------
EXTENDS TLC, Naturals, FiniteSets, Integers

CONSTANTS any, none, Replicas, Values, Ballots, Quorums
CONSTANTS FastQuorums, FastBallots

VARIABLES messages, decision, maxBallot, maxVBallot, maxValue

INSTANCE Paxos

ClassicBallots == Ballots \ FastBallots

FastAssume == /\ \A q \in FastQuorums : q \subseteq Replicas
              /\ \A q, r \in FastQuorums : q \intersect r # {}
              /\ \A q \in Quorums : \A r, s \in FastQuorums : q \intersect r \intersect s # {}

ASSUME PaxosAssume /\ FastAssume

IsMajorityValue(M, v) == Cardinality({m \in M : m.value = v}) > Cardinality(M) \div 2

\* Phase 2a (Any)
FastAccept ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in FastBallots :
        /\ p2bMessages = {} \* No proposed values yet.
        /\ SendMessage([type |-> "P2a",
                        ballot |-> b,
                        value |-> any])

\* Phase 2b (Any)
FastAccepted ==
    /\ UNCHANGED<<decision>>
    /\ \E a \in Replicas, m \in p2aMessages, v \in Values:
        /\ m.value = any
        /\ maxBallot[a] <= m.ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = v]
        /\ \A n \in p2bMessages : ~(n.ballot = m.ballot /\ n.acceptor = a)
        /\ SendMessage([type |-> "P2b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        value |-> v])

\* Phase 3 (Any)
FastDecide ==
    /\ UNCHANGED<<messages, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in FastBallots, q \in FastQuorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
            V == {w \in Values : \E m \in M : w = m.value}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ Cardinality(V) = 1
           /\ \E m \in M : decision' = m.value

\* Phase 2a
ClassicAccept ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in ClassicBallots, f \in FastBallots, q \in FastQuorums, v \in Values :
        /\ f < b \* There was a fast round before this classic round.
        /\ \A m \in p2aMessages : m.ballot # b
        /\ LET M == {m \in p2bMessages : m.ballot = f /\ m.acceptor \in q}
               V == {w \in Values : \E m \in M : w = m.value}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ Cardinality(V) > 1 \* Collision occured.
              /\ IF \E w \in V : IsMajorityValue(M, w)
                 THEN IsMajorityValue(M, v) \* Choose majority in quorum.
                 ELSE v \in V \* Choose any.
              /\ SendMessage([type |-> "P2a",
                              ballot |-> b,
                              value |-> v])

\* Phase 2b
ClassicAccepted == PaxosAccepted

\* Phase 3
ClassicDecide ==
    /\ UNCHANGED<<messages, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in ClassicBallots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = m.value

FastTypeOK == PaxosTypeOK

FastInit == PaxosInit

FastNext == \/ FastAccept
            \/ FastAccepted
            \/ FastDecide
            \/ ClassicAccept
            \/ ClassicAccepted
            \/ ClassicDecide
            \/ PaxosSuccess

FastSpec == /\ FastInit
            /\ [][FastNext]_<<messages, decision, maxBallot, maxVBallot, maxValue>>

FastNontriviality == decision = none \/ \E m \in p2bMessages : m.value = decision

FastConsistency == PaxosConsistency

FastSafetyProperty == /\ [][FastNontriviality]_<<messages, decision>>
                      /\ [][FastConsistency]_<<messages, decision>>

FastSymmetry == PaxosSymmetry

===============================================================