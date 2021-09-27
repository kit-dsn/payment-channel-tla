------------------------- MODULE PaymentChannelUser -------------------------

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
          AvailableTransactionIds,
          Time,
          Preimages,
          Amounts,
          MAX_TIME

VARIABLES State,
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
Ledger == INSTANCE Ledger


SignTransaction(transaction) ==
    LET signedInputs == {[input EXCEPT !.witness.signatures = @ \cup {Vars.MyKey}] : input \in transaction.inputs}
    IN  [transaction EXCEPT !.inputs = signedInputs]
    
NextTimedStepTime ==
    LET timelimits ==
        {
        \* Close channel and redeem HTLC if other party does not progress incoming HTLC that we have the preimage for
        \* Ignore HTLCs that have already timed out
        LET FulfilledIncomingHTLCs == {htlc \in Vars.IncomingHTLCs : htlc.state \in {"PENDING-COMMIT", "COMMITTED", "FULFILLED", "SENT-REMOVE"} /\ htlc.hash \in Inventory.preimages /\ htlc.absTimelock > LedgerTime } \* TODO can this be pending-commit or committed?
        IN IF Cardinality(FulfilledIncomingHTLCs) >= 1
           THEN (CHOOSE htlc \in FulfilledIncomingHTLCs : (\A otherHTLC \in FulfilledIncomingHTLCs : otherHTLC.absTimelock >= htlc.absTimelock)).absTimelock - 1
           ELSE 9999999,
        
        \* Redeem outgoing HTLC after other party has closed the channel with the HTLC
        LET UnfulfilledOutgoingHTLCs == {htlc \in Vars.OutgoingHTLCs : htlc.state \in {"PENDING-COMMIT", "COMMITTED"} /\ ~ htlc.hash \in Inventory.preimages }
        IN IF Cardinality(UnfulfilledOutgoingHTLCs) >= 1
           THEN (CHOOSE htlc \in UnfulfilledOutgoingHTLCs : (\A otherHTLC \in UnfulfilledOutgoingHTLCs : otherHTLC.absTimelock >= htlc.absTimelock)).absTimelock
           ELSE 9999999,
        
        \* Punish other party if an outdated commitment transaction has been published and not yet been punished (or close if we cannot punish and have nothing to loose)
        \* Choose only old transactions that have an output that becomes spendable for us finally (finally = MAX_TIME for now)
        LET otherOldTxInLedger == {oldTx \in LedgerTx : oldTx.id \in Vars.OldOtherCommitTXIds /\ Cardinality(Ledger!OnChainOutputSpendableByUser({oldTx}, Inventory, MAX_TIME)) > 0}
        IN IF Honest /\ Cardinality(otherOldTxInLedger) > 0 /\ State # "closed"
           THEN (CHOOSE oldTx \in otherOldTxInLedger : (\A otherOldTx \in otherOldTxInLedger : oldTx.publishedAt <= otherOldTx.publishedAt) ).publishedAt + 3 \* This assumes that each party reacts within 3 steps to outdated transactions
           ELSE 9999999,
        
        IF State # "closed"
        THEN MAX_TIME - 5
        ELSE 9999999
        }
    IN CHOOSE min \in timelimits : (\A time \in timelimits : min <= time)

SendFirstVars ==
    /\ State = "init"
    /\ State' = "open-sent-vars"
    /\ Balance > 0
    /\ Message = EmptyMessage
    /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                       !.type = "InitialData",
                                       !.data.key = Vars.MyKey,
                                       !.data.capacity = Balance,
                                       !.data.rKey = Vars.MyRKey]
    /\ Vars' = [Vars EXCEPT !.Capacity = Balance]
    /\ UNCHANGED <<Inventory, Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
                                       
ReplyToFirstVars ==
    /\ State = "init"
    /\ State' = "open-sent-vars"
    /\ Message.recipient = MyName
    /\ Message.type = "InitialData"
    /\ Message.data.capacity > 0
    /\ Vars' = [Vars EXCEPT !.OtherKey = Message.data.key,
                            !.Capacity = Message.data.capacity,
                            !.OtherRKey = Message.data.rKey]
    /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                       !.type = "InitialData",
                                       !.data.key = Vars.MyKey,
                                       !.data.rKey = Vars.MyRKey]
    /\ UNCHANGED <<Inventory, Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
                                       
CreateFundingTransaction ==
    /\ State = "open-sent-vars"
    /\ State' = "open-funding-created"
    /\ Message.recipient = MyName
    /\ Message.type = "InitialData"
    /\ LET fundingTxId == TIO!GetNewTransactionId
       IN /\ TIO!MarkAsUsed(fundingTxId)
          /\ LET fundingTransaction == 
                 [id |-> fundingTxId,
                  inputs |-> {[parentId |-> Vars.FundingInputTxId,
                               outputId |-> 1,
                               witness |-> [signatures |-> {Vars.MyKey}]]},
                  outputs |-> {[parentId |-> fundingTxId,
                                outputId |-> 1,
                                amount |-> Balance,
                                conditions |-> {Ledger!AllSignaturesCondition({Vars.MyKey, Message.data.key})}
                              ]}
                 ]
             IN /\ Inventory' = [Inventory EXCEPT !.transactions = @ \cup {fundingTransaction}]
                /\ Vars' = [Vars EXCEPT !.fundingTxId = fundingTransaction.id,
                                        !.OtherKey = Message.data.key,
                                        !.OtherRKey = Message.data.rKey]
    /\ UNCHANGED <<Message, Balance, LedgerTx, PendingBalance>>
    /\ UNCHANGED UnchangedVars
                 
SendFirstCommitTransaction ==
   /\ State = "open-funding-created"
   /\ State' = "open-sent-commit"
   /\ LET commitTxId == TIO!GetNewTransactionId
      IN /\ TIO!MarkAsUsed(commitTxId)
         /\ LET firstCommit ==
                         [id |-> commitTxId,
                          inputs |-> {[parentId |-> Vars.fundingTxId,
                                       outputId |-> 1,
                                       witness |-> [signatures |-> {Vars.MyKey}]]},
                           outputs |-> {[parentId |-> commitTxId,
                                        outputId |-> 1,
                                        amount |-> Balance,
                                        conditions |-> {Ledger!SingleSignatureCondition(Vars.MyKey)} ],
                                       [parentId |-> commitTxId,
                                        outputId |-> 2,
                                        amount |-> Vars.Capacity - Balance,
                                        conditions |-> {[Ledger!SingleSignatureCondition(Vars.OtherKey) EXCEPT !.relTimelock = 5],
                                                        Ledger!AllSignaturesCondition({Vars.MyKey, Vars.OtherRKey})}
                                      ]}
                         ]
            IN /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                                  !.type = "FirstCommitTransaction",
                                                  !.data.transaction = firstCommit,
                                                  !.data.fundingTxId = Vars.fundingTxId]
               /\ Vars' = [Vars EXCEPT !.CurrentOtherCommitTX = firstCommit]
    /\ UNCHANGED <<Inventory, Balance, LedgerTx, PendingBalance>>
    /\ UNCHANGED UnchangedVars
                                                  
ReplyToFirstCommitTransaction ==
    /\ State = "open-sent-vars"
    /\ State' = "open-sent-commit"
    /\ Message.recipient = MyName
    /\ Message.type = "FirstCommitTransaction"
    /\ Inventory' = [Inventory EXCEPT !.transactions = @ \cup {Message.data.transaction}]
    /\ LET commitTxId == TIO!GetNewTransactionId
       IN /\ TIO!MarkAsUsed(commitTxId)
          /\ LET firstCommit == [id |-> commitTxId,
                           inputs |-> {[parentId |-> Message.data.fundingTxId,
                                        outputId |-> 1,
                                        witness |-> [signatures |-> {Vars.MyKey}]]},
                           outputs |-> {[parentId |-> commitTxId,
                                         outputId |-> 1,
                                         amount |-> Balance,
                                         conditions |-> {Ledger!SingleSignatureCondition(Vars.MyKey)}
                                        ],
                                        [parentId |-> commitTxId,
                                         outputId |-> 2,
                                         amount |-> Vars.Capacity - Balance,
                                         conditions |-> {
                                            [Ledger!SingleSignatureCondition(Vars.OtherKey) EXCEPT !.relTimelock = 5],
                                            Ledger!AllSignaturesCondition({Vars.MyKey, Vars.OtherRKey})
                                         }
                                        ]
                                       }
                          ]
             IN /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                                   !.type = "FirstCommitTransaction",
                                                   !.data.transaction = firstCommit]
                /\ Vars' = [Vars EXCEPT !.CurrentOtherCommitTX = firstCommit,
                                        !.fundingTxId = Message.data.fundingTxId,
                                        !.LatestCommitTransactionId = Message.data.transaction.id,
                                        !.CommitmentTxIds = @ \cup {Message.data.transaction.id}]
    /\ UNCHANGED <<LedgerTx, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars

ReceiveCommitTransaction ==
    /\ State = "open-sent-commit"
    /\ State' = "open-recv-commit"
    /\ Message.recipient = MyName
    /\ Message.type = "FirstCommitTransaction"
    /\ Inventory' = [Inventory EXCEPT !.transactions = @ \cup {Message.data.transaction}]
    /\ Message' = EmptyMessage
    /\ Vars' = [Vars EXCEPT !.LatestCommitTransactionId = Message.data.transaction.id,
                            !.CommitmentTxIds = @ \cup {Message.data.transaction.id}]
    /\ UNCHANGED <<Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
PublishFundingTransaction ==
    /\ State = "open-recv-commit"
    /\ State' = "open-funding-pub"
    /\ \E tx \in Inventory.transactions : tx.id = Vars.fundingTxId
    /\ LET fundingTx == SignTransaction(CHOOSE tx \in Inventory.transactions : tx.id = Vars.fundingTxId)
       IN /\ Ledger!PublishTx(fundingTx)
          /\ Inventory' = [Inventory EXCEPT !.transactions = @ \ {fundingTx}]
    /\ UNCHANGED <<Message, Vars, Balance, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
          
NoteThatFundingTransactionPublished ==
    /\ State = "open-sent-commit"
    /\ State' = "open-funding-pub"
    (***********************************************************************
    This verifies that the funding transaction has been published on the blockchain.
    See CVE-2019-12998 / CVE-2019-12999 / CVE-2019-13000 and
    https://lists.linuxfoundation.org/pipermail/lightning-dev/2019-September/002174.html
     ***********************************************************************)
    /\ \E tx \in LedgerTx : tx.id = Vars.fundingTxId
    /\ UNCHANGED <<Message, Vars, Inventory, Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
SendNewRevocationKey ==
    /\ \/ State = "open-funding-pub" /\ State' = "open-new-key-sent"
       \/ State = "open-new-key-received" /\ State' = "rev-keys-exchanged"
       \/ State = "update-revoked-received" /\ State' = "update-new-key-sent"
       \/ State = "update-new-key-received" /\ State' = "rev-keys-exchanged"
    /\ LET newRevocationKey == [Vars.MyRKey EXCEPT !.Index = @ + 1]
       IN /\ Message = EmptyMessage
          /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                             !.type = "NewRKey",
                                             !.data.rKey = newRevocationKey]
          /\ Vars' = [Vars EXCEPT !.MyNewRKey = newRevocationKey]
          /\ Inventory' = [Inventory EXCEPT !.keys = @ \cup {newRevocationKey}]
    /\ UNCHANGED <<Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
ReceiveNewRevocationKey ==
    /\ \/ State = "open-funding-pub" /\ State' = "open-new-key-received"
       \/ State = "open-new-key-sent" /\ State' = "rev-keys-exchanged"
       \/ State = "update-revoked-received" /\ State' = "update-new-key-received"
       \/ State = "update-new-key-sent" /\ State' = "rev-keys-exchanged"
    /\ Message.recipient = MyName
    /\ Message.type = "NewRKey"
    /\ Message' = EmptyMessage
    /\ Vars' = [Vars EXCEPT !.OtherNewRKey = Message.data.rKey]
    /\ UNCHANGED <<Inventory, Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
UpdateRKeyInConditions(conditions, oldRKey, newRKey) ==
    {IF oldRKey \in condition.data.keys
     THEN [condition EXCEPT !.data.keys = (@ \ {oldRKey}) \cup {newRKey}]
     ELSE condition
     : condition \in conditions}
    
                    
HTLCsByStates(states) == {htlc \in (Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs) : htlc.state \in states}

\* from https://github.com/tlaplus/Examples/blob/master/specifications/lamport_mutex/Functions.tla
Injection(S,T) == { M \in [S -> T] : \A a,b \in S : M[a] = M[b] => a = b }
Surjection(S,T) == { M \in [S -> T] : \A t \in T : \E s \in S : M[s] = t }
Bijection(S,T) == Injection(S,T) \cap Surjection(S,T)
    
CreateHTLCTransactions(commitmentTransaction, newHTLCs, oldHTLCs) ==
    LET HTLCs == (newHTLCs \cup HTLCsByStates({"SENT-COMMIT", "PENDING-COMMIT", "COMMITTED", "SENT-REMOVE", "FULFILLED"})) \ oldHTLCs
        NewTransactionIds == TIO!GetNewTransactionIds(Cardinality(HTLCs), {commitmentTransaction.id})
        IdForHTLC == CHOOSE bijection \in Bijection(HTLCs, NewTransactionIds) : TRUE
    IN  { LET htlcTransactionId == IdForHTLC[htlc]
          IN  [id |-> htlcTransactionId,
           inputs |-> {[parentId |-> commitmentTransaction.id,
                        outputId |-> (CHOOSE output \in commitmentTransaction.outputs :
                                            (\E condition \in output.conditions :
                                                    /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                                                    /\ condition.data.hash = htlc.hash )
                                      ).outputId,
                        witness |-> [signatures |-> {Vars.MyKey}]]},
           outputs |-> {[parentId |-> htlcTransactionId,
                         outputId |-> 1,
                         amount |-> htlc.amount,
                         conditions |-> {
                            [Ledger!SingleSignatureCondition(Vars.OtherKey) EXCEPT !.relTimelock = 5],
                            Ledger!AllSignaturesCondition({Vars.MyKey, Vars.OtherNewRKey})
                         }
                        ]
                       }
          ]
        : htlc \in HTLCs}
    
SendSignedCommitmentWithHTLC ==
    /\ \/ State = "update-commitment-received" /\ State' = "update-commitment-signed-received"
       \/ State = "rev-keys-exchanged" /\ State' = "update-commitment-signed"
    /\ Message = EmptyMessage \* Make sure that other party has already processed previous message.
    /\ \E HTLCsToAdd \in SUBSET({htlcData \in HTLCsByStates({"NEW", "RECV-COMMIT"}) : LedgerTime < htlcData.absTimelock}) :
      /\ Cardinality(HTLCsToAdd) > 0
      /\ LET commitTxId == TIO!GetNewTransactionId
             htlcAmountToMe == Ledger!SumAmounts(HTLCsToAdd \cap Vars.IncomingHTLCs)
             htlcAmountToOther == Ledger!SumAmounts(HTLCsToAdd \cap Vars.OutgoingHTLCs)
             outputToMe == CHOOSE output \in Vars.CurrentOtherCommitTX.outputs : output.outputId = 1
             outputToOther == CHOOSE output \in Vars.CurrentOtherCommitTX.outputs : output.outputId = 2
         IN /\ outputToMe.amount >= htlcAmountToOther
            /\ outputToOther.amount >= htlcAmountToMe
            /\ LET newOutputIds == CHOOSE set \in SUBSET(IDs \ {output.outputId : output \in Vars.CurrentOtherCommitTX.outputs}) : Cardinality(set) = Cardinality(HTLCsToAdd)
                   IdForHTLCOutput == CHOOSE bijection \in Bijection(HTLCsToAdd, newOutputIds) : TRUE
                   newCommit ==
                        [Vars.CurrentOtherCommitTX
                         EXCEPT !.id = commitTxId,
                                !.outputs = {[output EXCEPT !.parentId = commitTxId, !.conditions = UpdateRKeyInConditions(@, Vars.OtherRKey, Vars.OtherNewRKey)] : output \in (@ \ {outputToMe, outputToOther})}
                                            \cup {[outputToMe EXCEPT !.parentId = commitTxId,
                                                                     !.amount = @ - htlcAmountToOther,
                                                                     !.conditions = UpdateRKeyInConditions(@, Vars.OtherRKey, Vars.OtherNewRKey) ]}
                                            \cup {[outputToOther EXCEPT !.parentId = commitTxId,
                                                                        !.amount = @ - htlcAmountToMe,
                                                                        !.conditions = UpdateRKeyInConditions(@, Vars.OtherRKey, Vars.OtherNewRKey) ]}
                                            \cup {[ parentId |-> commitTxId,
                                                    outputId |-> IdForHTLCOutput[htlcData],
                                                    amount |-> htlcData.amount,
                                                    conditions |-> {
                                                        (IF htlcData \in Vars.OutgoingHTLCs
                                                            THEN Ledger!AllSigHashLockCondition({Vars.MyKey, Vars.OtherKey}, htlcData.hash) \* spent by HTLC success transaction
                                                            ELSE Ledger!SingleSigHashLockCondition(Vars.MyKey, htlcData.hash)),
                                                        (IF htlcData \in Vars.OutgoingHTLCs
                                                            THEN [Ledger!SingleSignatureCondition(Vars.MyKey) EXCEPT !.absTimelock = htlcData.absTimelock]
                                                            ELSE [Ledger!AllSignaturesCondition({Vars.MyKey, Vars.OtherKey}) EXCEPT !.absTimelock = htlcData.absTimelock]), \* spent by HTLC timeout transaction
                                                        Ledger!AllSignaturesCondition({Vars.MyKey, Vars.OtherNewRKey})
                                                    }
                                                 ] : htlcData \in HTLCsToAdd}
                        ]
                   HTLCTransactions == CreateHTLCTransactions(newCommit, HTLCsToAdd, {})
               IN /\ TIO!MarkMultipleAsUsed({commitTxId} \cup {tx.id : tx \in HTLCTransactions})
                  /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                                     !.type = "NewSignedCommitment",
                                                     !.data.transaction = newCommit,
                                                     !.data.htlcTransactions = HTLCTransactions] 
                  /\ Vars' = [Vars EXCEPT !.CurrentOtherCommitTX = newCommit,
                                          !.CurrentOtherHTLCTransactionIds = {tx.id : tx \in HTLCTransactions},
                                          !.PendingOldOtherCommitTxIds = @ \cup {Vars.CurrentOtherCommitTX.id} \cup Vars.CurrentOtherHTLCTransactionIds,
                                          !.OutgoingHTLCs = (@ \ (HTLCsToAdd \cap Vars.OutgoingHTLCs)) \cup {[htlcData EXCEPT !.state = IF htlcData.state = "NEW" THEN "SENT-COMMIT" ELSE "PENDING-COMMIT"] : htlcData \in (HTLCsToAdd \cap Vars.OutgoingHTLCs)},
                                          !.IncomingHTLCs = (@ \ (HTLCsToAdd \cap Vars.IncomingHTLCs)) \cup {[htlcData EXCEPT !.state = IF htlcData.state = "NEW" THEN "SENT-COMMIT" ELSE "PENDING-COMMIT"] : htlcData \in (HTLCsToAdd \cap Vars.IncomingHTLCs)},
                                          !.OtherOldRKey = Vars.OtherRKey,
                                          !.OtherRKey = Vars.OtherNewRKey]
    /\ UNCHANGED <<Inventory, LedgerTx, LedgerTime, PendingBalance, Balance>>
    /\ UNCHANGED UnchangedVars
    
HashesInCommitTransaction(tx) ==
    {condition.data.hash :
        condition \in { condition \in UNION {output.conditions : output \in tx.outputs} : condition.type \in {AllSigHashLock, SingleSigHashLock} }
    }
    
ReceiveSignedCommitment == \* this is a more general version of ReceiveCommitTransaction
    /\ \/ Message.type = "NewSignedCommitment" /\ State = "update-commitment-signed" /\ State' = "update-commitment-signed-received"
       \/ Message.type = "NewSignedCommitment" /\ State = "rev-keys-exchanged" /\ State' = "update-commitment-received"
       \/ Message.type = "NewSignedCommitment2" /\ State = "rev-keys-exchanged" /\ State' = "update-commitment2-received"
       \/ Message.type = "NewSignedCommitment2" /\ State = "update-commitment2-signed" /\ State' = "update-commitment-signed-received"
    /\ Message.recipient = MyName
    /\ Inventory' = [Inventory EXCEPT !.transactions = @ \cup {Message.data.transaction} \cup Message.data.htlcTransactions]
    /\ Message' = EmptyMessage
    /\ LET lastCommitmentTx == CHOOSE tx \in Inventory.transactions : tx.id = Vars.LatestCommitTransactionId
           newlyCommittedHTLCs == {htlc \in HTLCsByStates({"NEW", "SENT-COMMIT"}) : htlc.hash \in HashesInCommitTransaction(Message.data.transaction) /\ ~htlc.hash \in HashesInCommitTransaction(lastCommitmentTx)}
       IN   Vars' = [Vars EXCEPT !.LatestCommitTransactionId = Message.data.transaction.id,
                                 !.CommitmentTxIds = @ \cup {Message.data.transaction.id},
                                 !.OutgoingHTLCs = (@ \ newlyCommittedHTLCs) \cup {[htlc EXCEPT !.state = IF htlc.state = "NEW" THEN "RECV-COMMIT" ELSE "PENDING-COMMIT"] : htlc \in (newlyCommittedHTLCs \cap Vars.OutgoingHTLCs)},
                                 !.IncomingHTLCs = (@ \ newlyCommittedHTLCs) \cup {[htlc EXCEPT !.state = IF htlc.state = "NEW" THEN "RECV-COMMIT" ELSE "PENDING-COMMIT"] : htlc \in (newlyCommittedHTLCs \cap Vars.IncomingHTLCs)}]
    /\ UNCHANGED <<LedgerTx, TIOUsedTransactionIds, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
RevokeAndAck ==
    /\ \/ State = "update-commitment-signed-received" /\ State' = "update-revoked"
       \/ State = "update-revocation-received" /\ State' = "update-revoked-received"
    /\ Message = EmptyMessage
    /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                       !.type = "RevokeAndAck",
                                       !.data.rSecretKey = Vars.MyRKey]
    /\ Vars' = [Vars EXCEPT !.MyRKey = Vars.MyNewRKey]
    /\ UNCHANGED <<Inventory, Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
ReceiveRevocationKey ==
    /\ \/ State = "update-commitment-signed-received" /\ State' = "update-revocation-received"
       \/ State = "update-revoked" /\ State' = "update-revoked-received"
    /\ Message.recipient = MyName
    /\ Message.type = "RevokeAndAck"
    /\ Message' = EmptyMessage
    /\ Message.data.rSecretKey = Vars.OtherOldRKey
    /\ Inventory' = [Inventory EXCEPT !.keys = @ \cup {Message.data.rSecretKey}]
    /\ LET lastCommitmentTx == CHOOSE tx \in Inventory.transactions : tx.id = Vars.LatestCommitTransactionId
           nowCommittedHTLCs == HTLCsByStates({"PENDING-COMMIT"})
           nowRemovedHTLCs == {htlc \in HTLCsByStates({"SENT-REMOVE"}) :
                                        ~ htlc.hash \in (HashesInCommitTransaction(lastCommitmentTx) \cup HashesInCommitTransaction(Vars.CurrentOtherCommitTX))}
       IN Vars' = [Vars EXCEPT !.OldOtherCommitTXIds = @ \cup Vars.PendingOldOtherCommitTxIds,
                               !.PendingOldOtherCommitTxIds = {},
                               !.OutgoingHTLCs = (@ \ (nowCommittedHTLCs \cup nowRemovedHTLCs)) \cup {[htlc EXCEPT !.state = "COMMITTED"] : htlc \in (nowCommittedHTLCs \cap Vars.OutgoingHTLCs)},
                               !.IncomingHTLCs = (@ \ (nowCommittedHTLCs \cup nowRemovedHTLCs)) \cup {[htlc EXCEPT !.state = "COMMITTED"] : htlc \in (nowCommittedHTLCs \cap Vars.IncomingHTLCs)}]
    /\ UNCHANGED <<Balance, PendingBalance, LedgerTx, TIOUsedTransactionIds>>
    /\ UNCHANGED UnchangedVars

SendSignedCommitmentWithoutHTLC ==
    /\ Message = EmptyMessage \* Make sure that other party has already processed previous message.
    /\ \/ State = "rev-keys-exchanged" /\ State' = "update-commitment2-signed"
       \/ State = "update-commitment2-received" /\ State' = "update-commitment-signed-received" 
    /\ \E HTLCsToRemove \in SUBSET(HTLCsByStates({"FULFILLED"})) :
      /\ Cardinality(HTLCsToRemove) > 0
      /\ LET commitTxId == TIO!GetNewTransactionId
             htlcAmountForMe == Ledger!SumAmounts(HTLCsToRemove \cap Vars.IncomingHTLCs)
             htlcAmountForOther == Ledger!SumAmounts(HTLCsToRemove \cap Vars.OutgoingHTLCs)
             outputToMe == CHOOSE output \in Vars.CurrentOtherCommitTX.outputs : output.outputId = 1
             outputToOther == CHOOSE output \in Vars.CurrentOtherCommitTX.outputs : output.outputId = 2
             htlcOutputsToRemove == { output \in Vars.CurrentOtherCommitTX.outputs : (\E condition \in output.conditions : condition.type \in {SingleSigHashLock, AllSigHashLock} /\ (\E htlc \in HTLCsToRemove : condition.data.hash = htlc.hash)) } 
             newCommit == [Vars.CurrentOtherCommitTX
                 EXCEPT !.id = commitTxId,
                        !.outputs = {[output EXCEPT !.parentId = commitTxId, !.conditions = UpdateRKeyInConditions(@, Vars.OtherRKey, Vars.OtherNewRKey)] : output \in (@ \ (htlcOutputsToRemove \cup {outputToMe, outputToOther}))}
                                    \cup {[outputToMe EXCEPT !.parentId = commitTxId,
                                                             !.amount = @ + htlcAmountForMe,
                                                             !.conditions = UpdateRKeyInConditions(@, Vars.OtherRKey, Vars.OtherNewRKey) ]}
                                    \cup {[outputToOther EXCEPT !.parentId = commitTxId,
                                                                !.amount = @ + htlcAmountForOther,
                                                                !.conditions = UpdateRKeyInConditions(@, Vars.OtherRKey, Vars.OtherNewRKey) ]}
                ]
             HTLCTransactions == CreateHTLCTransactions(newCommit, {}, HTLCsToRemove \cup HTLCsByStates({"SENT-REMOVE"}))
         IN /\ TIO!MarkMultipleAsUsed({commitTxId} \cup {tx.id : tx \in HTLCTransactions})
            /\ Message' = [EmptyMessage EXCEPT !.recipient = OtherName,
                                               !.type = "NewSignedCommitment2",
                                               !.data.transaction = newCommit,
                                               !.data.htlcTransactions = HTLCTransactions]
            /\ Vars' = [Vars EXCEPT !.CurrentOtherCommitTX = newCommit,
                                    !.CurrentOtherHTLCTransactionIds = {tx.id : tx \in HTLCTransactions},
                                    !.PendingOldOtherCommitTxIds = @ \cup {Vars.CurrentOtherCommitTX.id} \cup Vars.CurrentOtherHTLCTransactionIds,
                                    !.OutgoingHTLCs = (@ \ HTLCsToRemove) \cup {[htlc EXCEPT !.state = "SENT-REMOVE"] : htlc \in (HTLCsToRemove \cap Vars.OutgoingHTLCs)},
                                    !.IncomingHTLCs = (@ \ HTLCsToRemove) \cup {[htlc EXCEPT !.state = "SENT-REMOVE"] : htlc \in (HTLCsToRemove \cap Vars.IncomingHTLCs)},
                                    !.OtherOldRKey = Vars.OtherRKey,
                                    !.OtherRKey = Vars.OtherNewRKey]
    /\ UNCHANGED <<Inventory, LedgerTx, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
    
CloseChannel ==
    /\ State # "closed"
    /\ NextTimedStepTime = LedgerTime \* Close only when necessary (HTLC Timeout or end of simulation reached)
    /\ State' = "closed"
    /\ Cardinality(Inventory.transactions) > 0
    /\ \E tx \in Inventory.transactions :
        /\ tx.id = Vars.LatestCommitTransactionId
        /\ LET signedTx == SignTransaction(tx)
           IN Ledger!PublishTx(signedTx)
        /\ LET uncommittedOutgoingHTLCs == {htlc \in Vars.OutgoingHTLCs : ~htlc.hash \in HashesInCommitTransaction(tx) /\ htlc.state \in {"NEW", "SENT-COMMIT"}}
               uncommittedIncomingHTLCs == {htlc \in Vars.IncomingHTLCs : ~htlc.hash \in HashesInCommitTransaction(tx) /\ htlc.state \in {"NEW", "SENT-COMMIT"}}
               uncommittedOutgoingHTLCAmounts == Ledger!SumAmounts(uncommittedOutgoingHTLCs)
           IN /\ Balance' = Balance + uncommittedOutgoingHTLCAmounts
              /\ PendingBalance' = PendingBalance - uncommittedOutgoingHTLCAmounts
              /\ Vars' = [Vars EXCEPT !.OutgoingHTLCs = (@ \ uncommittedOutgoingHTLCs) \cup {[htlc EXCEPT !.state = "ABORTED"] : htlc \in uncommittedOutgoingHTLCs},
                                      !.IncomingHTLCs = (@ \ uncommittedIncomingHTLCs) \cup {[htlc EXCEPT !.state = "ABORTED"] : htlc \in uncommittedIncomingHTLCs} ]
    /\ UNCHANGED <<Message, Inventory, TIOUsedTransactionIds>>
    /\ UNCHANGED UnchangedVars
    
\* Note: 'Honestly' means with a state that cannot be revoked (i.e., the latest state or a pending state that has been superseded but not revoked) 
NoteThatOtherPartyClosedHonestly ==
    /\ State # "closed"
    /\  \/  /\ "id" \in DOMAIN Vars.CurrentOtherCommitTX
            /\ Vars.CurrentOtherCommitTX.id \in Ledger!LedgerTxIds
        \/ Cardinality(Vars.PendingOldOtherCommitTxIds \cap Ledger!LedgerTxIds) > 0
    /\ State' = "closed"
    /\ LET closingTx == CHOOSE tx \in LedgerTx : tx.id \in Vars.PendingOldOtherCommitTxIds \/ ("id" \in DOMAIN Vars.CurrentOtherCommitTX /\ tx.id = Vars.CurrentOtherCommitTX.id)
           uncommittedOutgoingHTLCs == {htlc \in Vars.OutgoingHTLCs : ~htlc.hash \in HashesInCommitTransaction(closingTx) /\ htlc.state \in {"NEW", "RECV-COMMIT", "SENT-COMMIT", "PENDING-COMMIT"}}
           uncommittedOutgoingHTLCAmounts == Ledger!SumAmounts(uncommittedOutgoingHTLCs)
       IN /\ Balance' = Balance + uncommittedOutgoingHTLCAmounts
          /\ PendingBalance' = PendingBalance - uncommittedOutgoingHTLCAmounts
          /\ Vars' = [Vars EXCEPT !.OutgoingHTLCs = (@ \ uncommittedOutgoingHTLCs) \cup {[htlc EXCEPT !.state = "ABORTED"] : htlc \in uncommittedOutgoingHTLCs} ]
    /\ UNCHANGED <<Message, Inventory, LedgerTx, TIOUsedTransactionIds>>
    /\ UNCHANGED UnchangedVars
    
\* Note: Cheating might not be punishable if we do not (and never had) any funds in the channel because punishment transactions cannot spend a 0-amount output
NoteThatOtherPartyClosedButUnpunishable ==
    /\ State # "closed"
    /\ Balance = 0
    /\ Cardinality(Vars.OldOtherCommitTXIds \cap Ledger!LedgerTxIds) > 0
    /\ \E oldCommitmentTx \in LedgerTx :
        /\ oldCommitmentTx.id \in Vars.OldOtherCommitTXIds
        /\ \E output \in oldCommitmentTx.outputs :
            /\ output.amount = 0
            /\ \E condition \in output.conditions :
                /\ condition.type = SingleSignature
                /\ condition.data.keys = {Vars.MyKey}
    /\ State' = "closed"
    /\ UNCHANGED <<Message, Vars, Inventory, Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
NoteThatPreimageOnChain ==
    /\ \E htlc \in Vars.OutgoingHTLCs :
        /\ ~ htlc.hash \in Inventory.preimages
        /\ \E output \in Ledger!LedgerOutputs(LedgerTx) :
            /\ \E condition \in output.conditions :
                /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                /\ htlc.hash = condition.data.hash
            /\ \E child \in LedgerTx :
                /\ \E input \in child.inputs :
                    /\ input.parentId = output.parentId
                    /\ input.outputId = output.outputId
                    /\ "preimage" \in DOMAIN input.witness
                    /\ ~ input.witness.preimage \in Inventory.preimages 
                    /\ Inventory' = [Inventory EXCEPT !.preimages = @ \cup {input.witness.preimage}]
    /\ UNCHANGED <<State, Message, Vars, Balance, LedgerTx, TIOUsedTransactionIds, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    
Subset1(set) == {{x} : x \in set}
ReduceSetToOne(set) == IF set = {} THEN set ELSE {CHOOSE x \in set : TRUE} 
MyWitnesses == [signatures: SUBSET Inventory.keys] \cup [signatures: SUBSET Inventory.keys, preimage: Inventory.preimages]
\* Only select witnesses that might match the given conditions
MyReducedWitnesses(selection) == [signatures: SUBSET (Inventory.keys \cap selection)] \cup [signatures: SUBSET (Inventory.keys \cap selection), preimage: Inventory.preimages]
MyPossibleTxInputs(parentSet) ==
    UNION {
        UNION {
            [parentId: {parent.id},
             outputId: {output.outputId},
             witness: IF \E witness \in MyReducedWitnesses(UNION {condition.data.keys : condition \in output.conditions}) : Ledger!WitnessMatchesConditions(witness, output.conditions, parent.publishedAt, LedgerTime)
                      THEN {CHOOSE witness \in MyReducedWitnesses(UNION {condition.data.keys : condition \in output.conditions}) : Ledger!WitnessMatchesConditions(witness, output.conditions, parent.publishedAt, LedgerTime)}
                      ELSE {}
             ] : output \in {output \in parent.outputs : output.amount > 0 /\ (~\E input \in Ledger!LedgerInputs(LedgerTx) : input.parentId = parent.id /\ input.outputId = output.outputId) } } : parent \in parentSet}
MyPossibleTxOutputs(parentId, amount) == [parentId: {parentId}, outputId: {1}, amount: {amount}, conditions: {{[type |-> SingleSignature, data |-> [keys |-> {Vars.MyKey}], absTimelock |-> 0, relTimelock |-> 0]}}]
MyPossibleNewTransactions(parentSet) == 
    LET txId == TIO!GetNewTransactionId
        txInputs == MyPossibleTxInputs(parentSet)
    IN IF txInputs = {} 
          THEN {}
          ELSE [id: {txId}, inputs: {txInputs}, outputs: Subset1(MyPossibleTxOutputs(txId, Ledger!AmountSpentByInputs(txInputs)))]
MyPossibleNewTransactionsWithoutOwnParents(parentSet) ==
    { tx \in MyPossibleNewTransactions(parentSet) :
        LET parents == Ledger!ConfirmedParentTx(tx)
        IN \E parent \in parents :
             \E output \in parent.outputs :
                 \E condition \in output.conditions :
                     \/ condition.type # SingleSignature
                     \/ condition.data.keys # {Vars.MyKey}
                     \/ condition.absTimelock > 0
                     \/ condition.relTimelock > 0
    }
    
RedeemHTLCAfterClose ==
    /\ State = "closed"
    /\ Cardinality(HTLCsByStates({"SENT-COMMIT", "PENDING-COMMIT", "COMMITTED", "SENT-REMOVE", "FULFILLED", "RECV-COMMIT"})) >= 1
    /\  \/ \E commitmentTx \in LedgerTx :
            \* Fulfill HTLCs in published commitment transaction that we know the preimage for
            \/  /\ commitmentTx.id \in (Vars.PendingOldOtherCommitTxIds \cup {Vars.CurrentOtherCommitTX.id} \cup Vars.CommitmentTxIds \cup Vars.CurrentOtherHTLCTransactionIds)
                /\ \E tx \in MyPossibleNewTransactionsWithoutOwnParents({commitmentTx}) :
                    /\ TIO!MarkAsUsed(tx.id)
                    /\ Ledger!PublishTx(tx)
                    /\ LET fulfilledHTLCs == {htlc \in (Vars.IncomingHTLCs \cup Vars.OutgoingHTLCs) :
                                                \E output \in commitmentTx.outputs :
                                                    \E input \in tx.inputs :
                                                        /\ input.parentId = commitmentTx.id
                                                        /\ input.outputId = output.outputId
                                                        /\ \E condition \in output.conditions :
                                                            /\ condition.type \in {SingleSigHashLock, AllSigHashLock}
                                                            /\ htlc.hash = condition.data.hash
                                                }
                       IN /\ Vars' = [Vars EXCEPT !.IncomingHTLCs = (@ \ fulfilledHTLCs) \cup {[htlc EXCEPT !.state = "FULFILLED"] : htlc \in (fulfilledHTLCs \cap Vars.IncomingHTLCs)},
                                                  !.OutgoingHTLCs = (@ \ fulfilledHTLCs) \cup {[htlc EXCEPT !.state = "FULFILLED"] : htlc \in (fulfilledHTLCs \cap Vars.OutgoingHTLCs)}
                                     ]
                          \* Newly received amount is the sum of amounts of HTLCs that have not yet been fulfilled
                          /\ LET receivedAmount == Ledger!SumAmounts({htlc \in fulfilledHTLCs : ~htlc.state \in {"FULFILLED", "SENT-REMOVE"} })
                             IN /\ Balance' = Balance + receivedAmount
                                /\ PendingBalance' = PendingBalance - receivedAmount
            \* Publish HTLC success or timeout transaction to redeem HTLC in published commitment transaction
            \/  /\ commitmentTx.id \in (Vars.PendingOldOtherCommitTxIds \cup {Vars.CurrentOtherCommitTX.id} \cup Vars.CommitmentTxIds \cup Vars.CurrentOtherHTLCTransactionIds)
                /\ \E tx \in Inventory.transactions :
                    /\ LET signedTransaction == SignTransaction(tx)
                       IN  \E htlc \in HTLCsByStates({"COMMITTED", "SENT-REMOVE", "SENT-COMMIT", "PENDING-COMMIT", "FULFILLED", "RECV-COMMIT"}) :
                              \E output \in commitmentTx.outputs :
                                /\ \E condition \in output.conditions : condition.type \in {SingleSigHashLock, AllSigHashLock} /\ condition.data.hash = htlc.hash
                                /\ \E input \in signedTransaction.inputs :
                                    /\ input.parentId = commitmentTx.id
                                    /\ input.outputId = output.outputId
                                    /\ LET isSuccessTransaction == \E condition \in output.conditions : condition.type = AllSigHashLock
                                           \* validTransaction adds the corresponding preimage to an existing HTLC success transaction 
                                           validTransaction == IF isSuccessTransaction
                                                                  THEN [signedTransaction EXCEPT !.inputs = {[inp EXCEPT !.witness = [signatures |-> inp.witness.signatures, preimage |-> htlc.hash]] : inp \in @}]
                                                                  ELSE signedTransaction
                                       IN   /\ Ledger!PublishTx(validTransaction)
                                            /\ Vars' = [Vars EXCEPT !.IncomingHTLCs = IF htlc \in Vars.IncomingHTLCs THEN (@ \ {htlc}) \cup {[htlc EXCEPT !.state = IF isSuccessTransaction THEN "FULFILLED" ELSE "TIMEDOUT"]} ELSE @, \* TODO only timeout fulfill incoming and 
                                                                    !.OutgoingHTLCs = IF htlc \in Vars.OutgoingHTLCs THEN (@ \ {htlc}) \cup {[htlc EXCEPT !.state = IF isSuccessTransaction THEN "FULFILLED" ELSE "TIMEDOUT"]} ELSE @  \* timeout outgoing? TODO
                                                       ]
                                            \* Change balance only if HTLC has not already been fulfilled
                                            /\ Balance' = Balance + IF ((isSuccessTransaction /\ htlc \in Vars.IncomingHTLCs) \/ ~isSuccessTransaction) /\ ~htlc.state \in {"FULFILLED", "SENT-REMOVE"} THEN htlc.amount ELSE 0
                                            /\ PendingBalance' = PendingBalance - IF ((isSuccessTransaction /\ htlc \in Vars.IncomingHTLCs) \/ ~isSuccessTransaction) /\ ~htlc.state \in {"FULFILLED", "SENT-REMOVE"} THEN htlc.amount ELSE 0
    /\ UNCHANGED <<State, Message, Inventory>>
    /\ UNCHANGED UnchangedVars
    
Cheat ==
    /\ Honest = FALSE
    /\ ~ ENABLED RedeemHTLCAfterClose
    /\  \/ \E tx \in Inventory.transactions :
            /\ tx.id # Vars.LatestCommitTransactionId \* This case would be closing
            /\ tx.id # Vars.fundingTxId
            /\ LET signedTx == SignTransaction(tx)
               IN Ledger!PublishTx(signedTx)
            /\ State' = "closed" \* Necessary because RedeemHTLCAfterClose requires State = "closed", might be removed if this restriction is lifted
            /\ UNCHANGED <<TIOUsedTransactionIds>>
        \/ \E tx \in MyPossibleNewTransactionsWithoutOwnParents(LedgerTx) :
            /\ TIO!MarkAsUsed(tx.id)
            /\ Ledger!PublishTx(tx)
            /\ UNCHANGED <<State>>
        \/ /\ \E tx \in LedgerTx : tx.id = Vars.fundingTxId
           /\ State' = "closed"
           /\ UNCHANGED <<LedgerTx, TIOUsedTransactionIds>>
    /\ Vars' = [Vars EXCEPT !.HaveCheated = TRUE]
    /\ UNCHANGED <<Message, Inventory, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars
    

Punish ==
    /\ Vars.HavePunished = FALSE
    /\ Cardinality(Vars.OldOtherCommitTXIds \cap Ledger!LedgerTxIds) > 0
    /\ Cardinality(MyPossibleNewTransactionsWithoutOwnParents({parent \in LedgerTx: parent.id \in Vars.OldOtherCommitTXIds})) > 0
    /\ \E tx \in MyPossibleNewTransactionsWithoutOwnParents({parent \in LedgerTx: parent.id \in Vars.OldOtherCommitTXIds}) :
        /\ TIO!MarkAsUsed(tx.id)
        /\ Ledger!PublishTx(tx)
        /\ LET parent == CHOOSE parent \in LedgerTx : \E input \in tx.inputs : parent.id = input.parentId \* This assumes that the revocation transaction has only one parent
               spentParent == [parent EXCEPT !.outputs = {output \in @ : \E input \in tx.inputs : input.parentId = parent.id /\ input.outputId = output.outputId}]
               punishedHashes == HashesInCommitTransaction(spentParent)
           IN Vars' = [Vars EXCEPT !.HavePunished = TRUE]
    /\ State' = "closed"
    /\ UNCHANGED <<Message, Inventory, Balance, PendingBalance>>
    /\ UNCHANGED UnchangedVars


Next ==
    \/ SendFirstVars
    \/ ReplyToFirstVars
    \/ CreateFundingTransaction
    \/ SendFirstCommitTransaction
    \/ ReplyToFirstCommitTransaction
    \/ ReceiveCommitTransaction
    \/ PublishFundingTransaction
    \/ NoteThatFundingTransactionPublished
    \/ SendNewRevocationKey
    \/ ReceiveNewRevocationKey
    \/ SendSignedCommitmentWithHTLC
    \/ ReceiveSignedCommitment
    \/ RevokeAndAck
    \/ ReceiveRevocationKey
    \/ SendSignedCommitmentWithoutHTLC
    \/ CloseChannel
    \/ NoteThatOtherPartyClosedHonestly
    \/ NoteThatOtherPartyClosedButUnpunishable
    \/ NoteThatPreimageOnChain
    \/ RedeemHTLCAfterClose
    \/ Cheat
    \/ Punish


=============================================================================
\* Modification History
\* Last modified Mon Sep 27 15:51:09 CEST 2021 by matthias
\* Created Tue Apr 13 11:49:06 CEST 2021 by matthias
