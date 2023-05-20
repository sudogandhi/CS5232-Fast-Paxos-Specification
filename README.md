# NUS CS5232 Research Project: Specifying Fast Paxos in TLA+

:confetti_ball: This TLA+ specification has been merged into the [Official TLA+ Examples Repository](https://github.com/tlaplus/Examples/tree/master/specifications/SimplifiedFastPaxos)! :confetti_ball:

## About

A simplified TLA+ specification of the Fast Paxos protocol by Leslie Lamport, a consensus algorithm for distributed systems. TLA+ is a high-level language for modeling programs and systems, especially concurrent and distributed ones, using simple mathematics.

## Software Prerequisites

Please, make sure to install
[Visual Studio Code](https://code.visualstudio.com/download) and its
[TLA+ Extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus),
following the instructions on the linked pages. Also, consider adding the
[following command](https://github.com/alygin/vscode-tlaplus/wiki/Automatic-Module-Parsing)
to your VSCode setting to parse your TLA+ code automatically.

## Running the TLA+ Model

After installing the TLA+ extension for VSCode, Simply open FastPaxos.tla or Paxos.tla in VSCode, right click anywhere in the file editor, and click "Check model with TLC".

## Estimated Model Verification Time

The following timings were achieved on a 6-core, 12-thread CPU:
- Paxos.tla: 4 seconds
- FastPaxos.tla: 1 minute 2 seconds
