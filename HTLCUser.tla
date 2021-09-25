------------------------------ MODULE HTLCUser ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS EmptyMessage,
          SingleSignature,
          AllSignatures,
          SingleSigHashLock,
          AllSigHashLock,
          IDs,
          Users,
          Keys,
          Hashes,
          Time,
          Preimages,
          AvailableTransactionIds,
          Amounts,
          MAX_TIME

VARIABLES State,
          PCState,
          Inventory,
          Vars,
          MyName,
          OtherName,
          Honest,
          Balance,
          PendingBalance,
          Message,
          LedgerTx,
          LedgerTime,
          TIOUsedTransactionIds,
          UnchangedVars

TIO == INSTANCE TransactionIdOracle 

RequestInvoice ==
    /\ State = "ready"
    /\ PCState = "rev-keys-exchanged"
    /\ State' = "invoice-requested"
    /\ Cardinality(Vars.NewPaymentData) > 0
    /\ Cardinality(Vars.OtherPaymentHashes) < Cardinality(Vars.NewPaymentData)
    /\ Message = EmptyMessage
    /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                       !.type = "RequestInvoice"]
    /\ UNCHANGED <<Inventory, Vars, LedgerTx, Balance, PendingBalance, TIOUsedTransactionIds>>
    /\ UNCHANGED UnchangedVars

GenerateAndSendPaymentHash ==
    /\ State = "ready"
    /\ Message.recipient = MyName
    /\ Message.type = "RequestInvoice"
    /\ LET preimage == TIO!GetNewTransactionId
       IN   /\ TIO!MarkAsUsed(preimage)
            /\ ~ preimage \in Inventory.preimages
            /\ LET hash == preimage
               IN /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                                     !.type = "PaymentHash",
                                                     !.data.hash = hash]
                  /\ Inventory' = [Inventory EXCEPT !.preimages = @ \cup {preimage}]
    /\ UNCHANGED <<State, Vars, LedgerTx, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
ReceivePaymentHash ==
    /\ State = "invoice-requested"
    /\ State' = "ready"
    /\ Message.recipient = MyName
    /\ Message.type = "PaymentHash"
    /\ Vars' = [Vars EXCEPT !.OtherPaymentHashes = @ \cup {Message.data.hash}]
    /\ Message' = EmptyMessage
    /\ UNCHANGED <<Inventory, LedgerTx, TIOUsedTransactionIds, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
AddAndSendOutgoingHTLC ==
    /\ State = "ready"
    /\ PCState = "rev-keys-exchanged"
    /\ State' = "update-htlc-sent"
    /\ Message = EmptyMessage
    /\ LedgerTime <= MAX_TIME - 10
    /\ \E payment \in Vars.NewPaymentData :
        /\ Balance >= payment.amount
        /\ \E hash \in Vars.OtherPaymentHashes :
            LET htlcData == [amount |-> payment.amount, hash |-> hash, absTimelock |-> LedgerTime + 5, state |-> "NEW"]
            IN  /\ Vars' = [Vars EXCEPT !.OutgoingHTLCs = @ \cup {htlcData},
                                        !.OtherPaymentHashes = @ \ {hash},
                                        !.NewPaymentData = @ \ {payment}]
                /\ PendingBalance' = PendingBalance + htlcData.amount
                /\ Balance' = Balance - htlcData.amount
                /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                                    !.type = "UpdateAddHTLC",
                                                    !.data.htlcData = htlcData]
    /\ UNCHANGED <<Inventory, LedgerTx, TIOUsedTransactionIds>>
    /\ UNCHANGED UnchangedVars
    
ReceiveUpdateAddHTLC ==
    /\ State = "ready"
    /\ State' = "update-htlc-added"
    /\ Message.recipient = MyName
    /\ Message.type = "UpdateAddHTLC"
    /\ LedgerTime < Message.data.htlcData.absTimelock - 1
    /\ LET newHTLC == [amount |-> Message.data.htlcData.amount, hash |-> Message.data.htlcData.hash, absTimelock |-> Message.data.htlcData.absTimelock, state |-> "NEW"]
       IN Vars' = [Vars EXCEPT !.IncomingHTLCs = @ \cup {newHTLC}]
    /\ Message' = EmptyMessage
    /\ UNCHANGED <<Inventory, LedgerTx, TIOUsedTransactionIds, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
SendHTLCPreimage ==
    /\ State = "update-htlc-added"
    /\ PCState = "rev-keys-exchanged"
    /\ State' = "ready"
    /\ Message = EmptyMessage
    /\ \E htlc \in {htlc \in Vars.IncomingHTLCs : htlc.state = "COMMITTED"} :
        /\ htlc.hash \in (Inventory.preimages \ Vars.OtherKnownPreimages)
        /\ LedgerTime < htlc.absTimelock
        /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                           !.type = "HTLCPreimage",
                                           !.data.preimage = htlc.hash]
        /\ Vars' = [Vars EXCEPT !.OtherKnownPreimages = @ \cup {htlc.hash},
                                !.IncomingHTLCs = (@ \ {htlc}) \cup {[htlc EXCEPT !.state = "FULFILLED"]} ]
        /\ Balance' = Balance + htlc.amount
        /\ PendingBalance' = PendingBalance - htlc.amount
    /\ UNCHANGED <<Inventory, LedgerTx, TIOUsedTransactionIds>>
    /\ UNCHANGED UnchangedVars
    
ReceiveHTLCPreimage ==
    /\ State = "update-htlc-sent"
    /\ State' = "ready"
    /\ Message.recipient = MyName
    /\ Message.type = "HTLCPreimage"
    /\ Message' = EmptyMessage
    /\ Inventory' = [Inventory EXCEPT !.preimages = @ \cup {Message.data.preimage}]
    /\ LET fulfilledHTLCs == {htlc \in (Vars.OutgoingHTLCs) : htlc.state = "COMMITTED" /\ htlc.hash = Message.data.preimage}
       IN Vars' = [Vars EXCEPT !.OutgoingHTLCs = (@ \ fulfilledHTLCs) \cup {[htlc EXCEPT !.state = "FULFILLED"] : htlc \in (fulfilledHTLCs \cap Vars.OutgoingHTLCs)} ]
    /\ UNCHANGED <<LedgerTx, TIOUsedTransactionIds, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars


Next ==
    \/ RequestInvoice
    \/ GenerateAndSendPaymentHash
    \/ ReceivePaymentHash
    \/ AddAndSendOutgoingHTLC
    \/ ReceiveUpdateAddHTLC
    \/ SendHTLCPreimage
    \/ ReceiveHTLCPreimage


=============================================================================
\* Modification History
\* Last modified Fri Sep 24 18:47:09 CEST 2021 by matthias
\* Created Thu Jun 10 13:36:19 CEST 2021 by matthias
