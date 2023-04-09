--------------------------- MODULE Paxos -----------------------------
(*
    Notes:
    1. Square brackets can be used to define a set of functions. [X -> Y]
    2. Curly brackets can be used to define a set of values. {x \in SUBSET X}
*)
EXTENDS TLC, Naturals, FiniteSets, Integers, Sequences

CONSTANTS any, none, Replicas, Values, Ballots, Quorums

VARIABLES messages \* Set of all messages sent.
VARIABLES decision \* Decided value of an acceptor.
VARIABLES maxBallot \* Maximum ballot an acceptor has seen.
VARIABLES maxVBallot \* Maximum ballot an acceptor has accepted.
VARIABLES maxValue \* Maximum value an acceptor has accepted.

P1aMessage == [type : {"P1a"},
               ballot : Ballots \ {0}]
P1bMessage == [type : {"P1b"},
               ballot : Ballots,
               acceptor : Replicas,
               maxVBallot : Ballots,
               maxValue : Values \union {none}] \* (maxVBallot = 0) <=> (maxValue = none)
P2aMessage == [type : {"P2a"},
               ballot : Ballots,
               value : Values \union {any}]
P2bMessage == [type : {"P2b"},
               ballot : Ballots,
               acceptor : Replicas,
               value : Values]
Message == P1aMessage \union P1bMessage \union P2aMessage \union P2bMessage

PaxosAssume == /\ IsFiniteSet(Replicas)
               /\ any \notin Values \union {none}
               /\ none \notin Values \union {any}
               /\ Ballots \subseteq Nat /\ 0 \in Ballots
               /\ \A q \in Quorums : q \subseteq Replicas
               /\ \A q, r \in Quorums : q \intersect r # {}

ASSUME PaxosAssume

p1aMessages == {m \in messages : m.type = "P1a"} \* Set of all P1a messages sent.
p1bMessages == {m \in messages : m.type = "P1b"} \* Set of all P1b messages sent.
p2aMessages == {m \in messages : m.type = "P2a"} \* Set of all P2a messages sent.
p2bMessages == {m \in messages : m.type = "P2b"} \* Set of all P2b messages sent.

ForcedValue(M) == (CHOOSE m \in M : \A n \in M : n.maxVBallot <= m.maxVBallot).maxValue

SendMessage(m) == messages' = messages \union {m}

\* Phase 1a
PaxosPrepare ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots \ {0} :
        SendMessage([type |-> "P1a",
                     ballot |-> b])

\* Phase 1b
PaxosPromise ==
    /\ UNCHANGED<<decision, maxVBallot, maxValue>>
    /\ \E a \in Replicas, m \in p1aMessages :
        /\ maxBallot[a] < m.ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ SendMessage([type |-> "P1b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        maxVBallot |-> maxVBallot[a],
                        maxValue |-> maxValue[a]])

\* Phase 2a
PaxosAccept ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots, q \in Quorums, v \in Values :
        /\ \A m \in p2aMessages : ~(m.ballot = b)
        /\ LET M == {m \in p1bMessages : m.ballot = b /\ m.acceptor \in q}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ \/ \A m \in M : m.maxValue = none
                 \/ v = ForcedValue(M)
              /\ SendMessage([type |-> "P2a",
                              ballot |-> b,
                              value |-> v])

\* Phase 2b
PaxosAccepted ==
    /\ UNCHANGED<<decision>>
    /\ \E a \in Replicas, m \in p2aMessages :
        /\ m.value \in Values
        /\ maxBallot[a] <= m.ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = m.value]
        /\ SendMessage([type |-> "P2b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        value |-> m.value])

\* Phase 3
PaxosDecide ==
    /\ UNCHANGED<<messages, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = m.value

PaxosSuccess ==
    /\ UNCHANGED<<messages, decision, maxBallot, maxVBallot, maxValue>>
    /\ decision \in Values
    /\ Print(Append("Success! Value: ", ToString(decision)), TRUE)

PaxosInit == /\ messages = {}
             /\ decision = none
             /\ maxBallot = [r \in Replicas |-> 0]
             /\ maxVBallot = [r \in Replicas |-> 0]
             /\ maxValue = [r \in Replicas |-> none]

PaxosNext == \/ PaxosPrepare
             \/ PaxosPromise
             \/ PaxosAccept
             \/ PaxosAccepted
             \/ PaxosDecide
             \/ PaxosSuccess

PaxosSpec == /\ PaxosInit
             /\ [][PaxosNext]_<<messages, decision, maxBallot, maxVBallot, maxValue>>
             /\ SF_<<messages, decision, maxBallot, maxVBallot, maxValue>>(PaxosSuccess)

PaxosTypeOK == /\ messages \subseteq Message
               /\ decision \in Values \union {none}
               /\ maxBallot \in [Replicas -> Ballots]
               /\ maxVBallot \in [Replicas -> Ballots]
               /\ maxValue \in [Replicas -> Values \union {none}]

PaxosNontriviality ==
    /\ \/ decision = none
       \/ \E m \in p2aMessages : m.value = decision
    /\ \A m \in p1bMessages : /\ m.maxValue \in Values \/ 0 = m.maxVBallot
                              /\ m.maxValue = none \/ 0 < m.maxVBallot

PaxosConsistency == decision = none \/ decision = decision'

PaxosSafetyProperty == /\ [][PaxosNontriviality]_<<messages, decision>>
                       /\ [][PaxosConsistency]_<<messages, decision>>

PaxosSymmetry == Permutations(Values) \union Permutations(Replicas)

===============================================================