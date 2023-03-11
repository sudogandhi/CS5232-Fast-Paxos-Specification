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

\* Variable messages is the set of all messages sent.
VARIABLES messages
\* Variable decision is the decided value of the replicas.
VARIABLES decision

PaxosQuorums == {q \in SUBSET Replicas : (Cardinality(Replicas) \div 2) < Cardinality(q)}

P1aMessage == [type : {"P1a"},
               ballot : Ballots,
               proposer : Replicas]
P1bMessage == [type : {"P1b"},
               ballot : Ballots,
               proposer : Replicas,
               acceptor : Replicas,
               acceptedBallot : Ballots \union {None},
               acceptedValue : Values \union {None}]
P2aMessage == [type : {"P2a"},
               ballot : Ballots,
               proposer : Replicas,
               value : Values]
P2bMessage == [type : {"P2b"},
               ballot : Ballots,
               proposer : Replicas,
               acceptor : Replicas,
               value : Values]
P3Message == [type : {"P3"},
              ballot : Ballots,
              proposer : Replicas,
              value : Values]
Message == P1aMessage \union P1bMessage \union P2aMessage \union P2bMessage \union P3Message

QuorumAssume == /\ \A q \in PaxosQuorums : q \subseteq Replicas
                /\ \A q1, q2 \in PaxosQuorums : q1 \intersect q2 # {}
BallotAssume == /\ Ballots \subseteq Nat
                /\ 0 \in Ballots
ASSUME /\ QuorumAssume /\ BallotAssume

Filter(M, f(_)) == {m \in M : f(m)}
FilterProposer(M, p) == Filter(M, LAMBDA m : m.proposer = p)
FilterAcceptor(M, a) == Filter(M, LAMBDA m : m.acceptor = a)
FilterType(M, t) == Filter(M, LAMBDA m : m.type = t)
P1aMessages == FilterType(messages, "P1a")
P1bMessages == FilterType(messages, "P1b")
P2aMessages == FilterType(messages, "P2a")
P2bMessages == FilterType(messages, "P2b")

HasLargestBallot(M, m) == \A n \in M : n.ballot < m.ballot
LargestBallotMessage(M) == CHOOSE m \in M : HasLargestBallot(M, m)
AcceptedBallot(a) == LET M == FilterAcceptor(P2bMessages, a)
                     IN IF M = {} THEN None ELSE LargestBallotMessage(M).ballot
AcceptedValue(a) == LET M == FilterAcceptor(P2bMessages, a)
                    IN IF M = {} THEN None ELSE LargestBallotMessage(M).value

SendMessage(m) == messages' = messages \union {m}

DecideValue(r, v) == decision' = [decision EXCEPT ![r] = v]

\* Phase 1a
\* A proposer sends a P1a message.
PaxosPrepare == \E b \in Ballots, p \in Replicas :
                    /\ \A m \in FilterProposer(P1aMessages, p) : b > m.ballot
                    /\ SendMessage([type |-> "P1a", ballot |-> b, proposer |-> p])
                    /\ UNCHANGED<<decision>>

\* Phase 1b
\* If an acceptor receives a P1a message,
\* with a ballot number larger than any P1a or P2a ballot it has seen before,
\* then it replies with a P1b message.
PaxosPromise == \E m \in P1aMessages, a \in Replicas :
                    /\ HasLargestBallot(FilterAcceptor(P1bMessages, a) \union
                                        FilterAcceptor(P2bMessages, a), m)
                    /\ SendMessage([type |-> "P1b",
                                    ballot |-> m.ballot,
                                    proposer |-> m.proposer,
                                    acceptor |-> a,
                                    acceptedBallot |-> AcceptedBallot(a),
                                    acceptedValue |-> AcceptedValue(a)])
                    /\ UNCHANGED<<decision>>

\* Phase 2a
PaxosAccept == FALSE
                \* Free Case:
                \* for all 1b replies, acceptedValue = None, acceptedBallot = None
                \* 2a message can have any value

                \* Forced Case:
                \* There exists 1b reply where acceptedValue != None AND acceptedBallot != None
                \* 2a message value must be value of reply with highest acceptedBallot

\* Phase 2b
PaxosAccepted == FALSE
                \* largest received so far < new ballot number
                \* Update value, update largest ballot number
                \* send old largest ballot number,
                \* send old value

\* Phase 3
PaxosDecide == FALSE
                \* Send decided value

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

DecideConflict == \E a, b \in Replicas : /\ decision[a] # None
                                         /\ decision[b] # None
                                         /\ decision[a] # decision[b]

DecideChange == \E a \in Replicas : /\ decision[a] # None
                                    /\ decision[a] # decision'[a]

InvalidAccepted == \E m \in P2bMessages :
                       \/ m.acceptedBallot = None /\ m.acceptedValue # None
                       \/ m.acceptedBallot # None /\ m.acceptedValue = None
                       \/ /\ m.acceptedBallot # None \/ m.acceptedValue # None
                          /\ \A n \in P2aMessages : /\ m.acceptedBallot # n.ballot
                                                    /\ m.acceptedValue # n.value

PaxosSafetyProperty == /\ [][~DecideChange]_<<messages, decision>>
                       /\ [][~DecideConflict]_<<messages, decision>>
                       /\ [][~InvalidAccepted]_<<messages, decision>>

PaxosLivenessProperty == TRUE

PaxosSymmetry == Permutations(Values) \union Permutations(Replicas)

===============================================================