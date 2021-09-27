# Specification of Protocol for Payment Channel in TLA+

Payment channels can be used to perform transactions between two parties instead of using a global blockchain.
This repository contains a TLA+ specification of a protocol for payment channels that is based on the Lightning Network's protocol.

[PaymentChannel.tla](PaymentChannel.tla) is the main file that specifies the initial state `INIT`, the `NEXT` action and the invariants and temporal properties.
[PaymentChannelUser.tla](PaymentChannelUser.tla) specifies all actions that can be performed by one of the participating users of the payment channel to open, update, and close the payment channel.
[HTLCUser.tla](HTLCUser.tla) specifies the actions to use HTLCs to make transactions over the payment channel. Once an HTLC has been added, the payment channel is updated to a state that includes the HTLC.
After the HTLC has been resolved or when it times out, the payment channel is updated to a state that removes the HTLC.
[Ledger.tla](Ledger.tla) specifies transactions and the ledger.
[TransactionIdOracle.tla](TransactionIdOracle.tla) includes helpers to assign unique transaction IDs to each transaction.

To check the specification using TLC, run
```
java -cp /path/to/tla2tools.jar tlc2.TLC PaymentChannel.toolbox/Model_1/MC.tla -workers auto -deadlock

```

