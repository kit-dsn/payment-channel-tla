\* This specification aims to help in understanding off-chain protocols, e.g. by specifying them thoroughly and by easily detecting
\* errors and showing how they can be exploited.
\*

--------------------------- MODULE PaymentChannel ---------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANT UserA,
         UserB,
         UserARev,
         UserBRev,
         NullUser,
         SingleSignature,
         AllSignatures,
         SingleSigHashLock,
         AllSigHashLock,
         MAX_TIME

VARIABLES LedgerTx,
          LedgerTime,
          AliceInventory,
          BobInventory,
          AliceVars,
          BobVars,
          AlicePCState,
          BobPCState,
          AliceHTLCState,
          BobHTLCState,
          AliceHonest,
          BobHonest,
          AliceBalance,
          BobBalance,
          PendingBalance,
          TIOUsedTransactionIds,
          Message

Users == {UserA, UserB, NullUser}
RevocationKeys == [Base: {UserARev, UserBRev}, Index: 0..100]
Keys == Users \cup RevocationKeys
Hashes == 0..200 \* TODO merge with Preimages and IDs
Preimages == 0..200
Time == 0..100
IDs == 1..200
Amounts == 0..20


TIO == INSTANCE TransactionIdOracle WITH AvailableTransactionIds <- 0..10
Ledger == INSTANCE Ledger

Subset1(set) == {{x} : x \in set}

TypeOK == /\ Ledger!TypeOK
          /\ AliceInventory \in [keys: SUBSET Keys, preimages: SUBSET Preimages, transactions: SUBSET Ledger!Transactions]
          /\ BobInventory \in [keys: SUBSET Keys, preimages: SUBSET Preimages, transactions: SUBSET Ledger!Transactions]
          /\ TIO!TypeOK
          /\ Message.recipient \in Users
          
EmptyMessage ==
    [recipient |-> NullUser,
        type |-> "",
        data |-> [key |-> NullUser, rKey |-> NullUser, rSecretKey |-> NullUser, capacity |-> 0,
            transaction |-> 0, htlcTransactions |-> {}, fundingTxId |-> 0,
            htlcData |-> 0, hash |-> 0, preimage |-> 0]]
          
Init ==
    /\ LedgerTx = {
       [id |-> 1,
        inputs |-> {
            [parentId |-> 1,
             outputId |-> 1,
             witness |-> [signatures |-> {UserA}]]},
        outputs |-> {
           [parentId |-> 1,
            outputId |-> 1,
            amount |-> 10,
            conditions |-> {
                [type |-> SingleSignature,
                 data |-> [keys |-> {UserA}],
                 absTimelock |-> 0,
                 relTimelock |-> 0]} ]},
        publishedAt |-> 0]
       }
    /\ LedgerTime = 1
    /\ TIOUsedTransactionIds = {1,2}
    /\ AliceInventory = [
        keys |-> {UserA},
        preimages |-> {},
        transactions |-> {}]
    /\ BobInventory = [
        keys |-> {UserB},
        preimages |-> {},
        transactions |-> {}]
    /\ AliceVars = [
        MyKey |-> UserA,
        MyRKey |-> [Base |-> UserARev, Index |-> 1],
        MyNewRKey |-> [null |-> 0],
        OtherKey |-> 0,
        Capacity |-> 0,
        FundingInputTxId |-> 1,
        OtherRKey |-> 0,
        OtherOldRKey |-> [null |-> 0],
        OtherNewRKey |-> [null |-> 0],
        fundingTxId |-> 0,
        CurrentOtherCommitTX |-> [null |-> 0],
        OtherPaymentHashes |-> {},
        PendingOldOtherCommitTxIds |-> {},
        OldOtherCommitTXIds |-> {},
        LatestCommitTransactionId |-> 0,
        CommitmentTxIds |-> {},
        CurrentOtherHTLCTransactionIds |-> {},
        HaveCheated |-> FALSE,
        HavePunished |-> FALSE,
        NewPaymentData |-> {[amount |-> 7]},
        OtherKnownPreimages |-> {},
        IncomingHTLCs |-> {},
        OutgoingHTLCs |-> {},
        Debug |-> {} ]
    /\ BobVars = [
        MyKey |-> UserB,
        MyRKey |-> [Base |-> UserBRev, Index |-> 1],
        MyNewRKey |-> [null |-> 0],
        OtherKey |-> 0,
        Capacity |-> 0,
        OtherRKey |-> 0,
        OtherOldRKey |-> [null |-> 0],
        OtherNewRKey |-> [null |-> 0],
        fundingTxId |-> 0,
        CurrentOtherCommitTX |-> [null |-> 0],
        OtherPaymentHashes |-> {},
        PendingOldOtherCommitTxIds |-> {}, 
        OldOtherCommitTXIds |-> {},
        LatestCommitTransactionId |-> 0,
        CommitmentTxIds |-> {},
        CurrentOtherHTLCTransactionIds |-> {},
        HaveCheated |-> FALSE,
        HavePunished |-> FALSE,
        NewPaymentData |-> {[amount |-> 3], [amount |-> 2]},
        OtherKnownPreimages |-> {},
        IncomingHTLCs |-> {},
        OutgoingHTLCs |-> {},
        Debug |-> {} ] 
    /\ AlicePCState = "init"
    /\ BobPCState = "init"
    /\ AliceHTLCState = "init"
    /\ BobHTLCState = "init"
    /\  \/ AliceHonest = TRUE /\ BobHonest = TRUE
        \/ AliceHonest = FALSE /\ BobHonest = TRUE
        \/ AliceHonest = TRUE /\ BobHonest = FALSE
    /\ AliceBalance = 10
    /\ BobBalance = 0
    /\ PendingBalance = 0
    /\ Message = EmptyMessage



AlicePC == INSTANCE PaymentChannelUser WITH State <- AlicePCState,
                                          Inventory <- AliceInventory,
                                          Honest <- AliceHonest,
                                          Vars <- AliceVars,
                                          MyName <- UserA,
                                          OtherName <- UserB,
                                          Balance <- AliceBalance,
                                          AvailableTransactionIds <- 30..69,
                                          UnchangedVars <- <<AliceHTLCState, LedgerTime, BobPCState, BobHTLCState, BobHonest, BobInventory, BobVars, BobBalance, AliceHonest>>
BobPC == INSTANCE PaymentChannelUser WITH State <- BobPCState,
                                        Inventory <- BobInventory,
                                        Honest <- BobHonest,
                                        Vars <- BobVars,
                                        MyName <- UserB,
                                        OtherName <- UserA,
                                        Balance <- BobBalance,
                                        AvailableTransactionIds <- 130..169,
                                        UnchangedVars <- <<BobHTLCState, LedgerTime, AlicePCState, AliceHTLCState, AliceHonest, AliceInventory, AliceVars, AliceBalance, BobHonest>>
AliceHTLC == INSTANCE HTLCUser WITH State <- AliceHTLCState,
                                    PCState <- AlicePCState,
                                          Inventory <- AliceInventory,
                                          Honest <- AliceHonest,
                                          Vars <- AliceVars,
                                          MyName <- UserA,
                                          OtherName <- UserB,
                                          Balance <- AliceBalance,
                                          AvailableTransactionIds <- 70..89,
                                          UnchangedVars <- <<AlicePCState, LedgerTime, BobPCState, BobHTLCState, BobHonest, BobInventory, BobVars, BobBalance, AliceHonest>>
BobHTLC == INSTANCE HTLCUser WITH State <- BobHTLCState,
                                    PCState <- BobPCState,
                                        Inventory <- BobInventory,
                                        Honest <- BobHonest,
                                        Vars <- BobVars,
                                        MyName <- UserB,
                                        OtherName <- UserA,
                                        Balance <- BobBalance,
                                        AvailableTransactionIds <- 170..189,
                                        UnchangedVars <- <<BobPCState, LedgerTime, AlicePCState, AliceHTLCState, AliceHonest, AliceInventory, AliceVars, AliceBalance, BobHonest>>

AdvanceLedgerTime ==
    /\ LedgerTime' \in {i \in 0..MAX_TIME :
        /\ i > LedgerTime
        /\ i <= AlicePC!NextTimedStepTime
        /\ i <= BobPC!NextTimedStepTime
        /\ (i \in {AlicePC!NextTimedStepTime, BobPC!NextTimedStepTime, MAX_TIME} ) }                                                \* TODO mehr Zeitschritte erlauben // Performancegewinn durch Beschränkung auf +1-Schritte?
    /\ UNCHANGED <<LedgerTx, AliceInventory, BobInventory, AliceVars, BobVars, AlicePCState, BobPCState, AliceHTLCState, BobHTLCState, AliceHonest, BobHonest, AliceBalance, BobBalance, PendingBalance, TIOUsedTransactionIds, Message>> 

BobsOnChainBalance(ledger, time) == Ledger!SumAmounts({outputWithParent.output : outputWithParent \in Ledger!OnChainOutputSpendableByUser(ledger, BobInventory, time)})
AlicesOnChainBalance(ledger, time) == Ledger!SumAmounts({outputWithParent.output : outputWithParent \in Ledger!OnChainOutputSpendableByUser(ledger, AliceInventory, time)})

                                                                     
AliceReadyForPayment ==
    /\ AlicePCState = "rev-keys-exchanged"
    /\ AliceHTLCState = "init"
    /\ AliceHTLCState' = "ready"
    /\ UNCHANGED <<LedgerTx, Message, PendingBalance, TIOUsedTransactionIds, AlicePCState, AliceInventory, AliceVars, AliceBalance>>
    /\ UNCHANGED <<LedgerTime, BobPCState, BobHTLCState, BobHonest, BobInventory, BobVars, BobBalance, AliceHonest>>
  
BobReadyForPayment ==
    /\ BobPCState = "rev-keys-exchanged"
    /\ BobHTLCState = "init"
    /\ BobHTLCState' = "ready"
    /\ UNCHANGED <<LedgerTx, Message, PendingBalance, TIOUsedTransactionIds, BobPCState, BobInventory, BobVars, BobBalance>>
    /\ UNCHANGED <<LedgerTime, AlicePCState, AliceHTLCState, AliceHonest, AliceInventory, AliceVars, AliceBalance, BobHonest>>
    
Next ==
    \/ AdvanceLedgerTime
    \/ AlicePC!SendFirstVars
    \/ AlicePC!ReplyToFirstVars
    \/ AlicePC!CreateFundingTransaction
    \/ AlicePC!SendFirstCommitTransaction
    \/ AlicePC!ReplyToFirstCommitTransaction
    \/ AlicePC!ReceiveCommitTransaction
    \/ AlicePC!PublishFundingTransaction
    \/ AlicePC!NoteThatFundingTransactionPublished
    \/ AlicePC!SendNewRevocationKey
    \/ AlicePC!ReceiveNewRevocationKey
    \/ AlicePC!SendSignedCommitmentWithHTLC
    \/ AlicePC!ReceiveSignedCommitment
    \/ AlicePC!RevokeAndAck
    \/ AlicePC!ReceiveRevocationKey
    \/ AlicePC!SendSignedCommitmentWithoutHTLC
    \/ AlicePC!CloseChannel
    \/ AlicePC!NoteThatOtherPartyClosedHonestly
    \/ AlicePC!NoteThatOtherPartyClosedButUnpunishable
    \/ AlicePC!NoteThatPreimageOnChain
    \/ AlicePC!RedeemHTLCAfterClose
    \/ AlicePC!Cheat
    \/ AlicePC!Punish
    \/ BobPC!SendFirstVars
    \/ BobPC!ReplyToFirstVars
    \/ BobPC!CreateFundingTransaction
    \/ BobPC!SendFirstCommitTransaction
    \/ BobPC!ReplyToFirstCommitTransaction
    \/ BobPC!ReceiveCommitTransaction
    \/ BobPC!PublishFundingTransaction
    \/ BobPC!NoteThatFundingTransactionPublished
    \/ BobPC!SendNewRevocationKey
    \/ BobPC!ReceiveNewRevocationKey
    \/ BobPC!SendSignedCommitmentWithHTLC
    \/ BobPC!ReceiveSignedCommitment
    \/ BobPC!RevokeAndAck
    \/ BobPC!ReceiveRevocationKey
    \/ BobPC!SendSignedCommitmentWithoutHTLC
    \/ BobPC!CloseChannel
    \/ BobPC!NoteThatOtherPartyClosedHonestly
    \/ BobPC!NoteThatOtherPartyClosedButUnpunishable
    \/ BobPC!NoteThatPreimageOnChain
    \/ BobPC!RedeemHTLCAfterClose
    \/ BobPC!Cheat
    \/ BobPC!Punish
    \/ AliceReadyForPayment
    \/ BobReadyForPayment
    \/ AliceHTLC!RequestInvoice
    \/ AliceHTLC!GenerateAndSendPaymentHash
    \/ AliceHTLC!ReceivePaymentHash
    \/ AliceHTLC!AddAndSendOutgoingHTLC
    \/ AliceHTLC!ReceiveUpdateAddHTLC
    \/ AliceHTLC!SendHTLCPreimage
    \/ AliceHTLC!ReceiveHTLCPreimage
    \/ BobHTLC!RequestInvoice
    \/ BobHTLC!GenerateAndSendPaymentHash
    \/ BobHTLC!ReceivePaymentHash
    \/ BobHTLC!AddAndSendOutgoingHTLC
    \/ BobHTLC!ReceiveUpdateAddHTLC
    \/ BobHTLC!SendHTLCPreimage
    \/ BobHTLC!ReceiveHTLCPreimage

Spec ==
    /\ Init
    /\ [][Next]_<<LedgerTime, LedgerTx, AliceInventory, BobInventory, AliceVars, BobVars, AlicePCState, BobPCState, AliceHTLCState, BobHTLCState, AliceHonest, BobHonest, AliceBalance, BobBalance, PendingBalance, TIOUsedTransactionIds, Message>>
    /\ WF_<<LedgerTime, LedgerTx, AliceInventory, BobInventory, AliceVars, BobVars, AlicePCState, BobPCState, AliceHTLCState, BobHTLCState, AliceBalance, BobBalance, PendingBalance, TIOUsedTransactionIds, Message>>(Next)


AllLedgerTxValid == \A tx \in LedgerTx : Ledger!TxValid(tx, LedgerTx)

\* Verification that a user has only the correct balance except if the other user cheated
\* This might be temporarily violated but must be valid in the end
AliceCanNotCheat ==
    <> [] ( \/ BobVars.HaveCheated
            \/ AlicesOnChainBalance(LedgerTx, LedgerTime) <= AliceBalance + PendingBalance)
BobCanNotCheat ==
    <> [] ( \/ AliceVars.HaveCheated
            \/ BobsOnChainBalance(LedgerTx, LedgerTime) <= BobBalance + PendingBalance)
TimeProgresses == <> (LedgerTime >= MAX_TIME)

\* Only UserBalance is guaranteed. No guarantee for PendingBalance.
AliceGetsBalance ==
    <> [] ( (~AliceVars.HaveCheated) => AlicesOnChainBalance(LedgerTx, MAX_TIME + 5) >= AliceBalance)
BobGetsBalance ==
    <> [] ( (~BobVars.HaveCheated) => BobsOnChainBalance(LedgerTx, MAX_TIME + 5) >= BobBalance)

FinallyNoPendingBalance == <> [] (AliceVars.HaveCheated \/ BobVars.HaveCheated \/ PendingBalance = 0)
\* TODO can we extend this to cheating?

PendingBalanceIsPositive == PendingBalance >= 0

BalancesAddUp ==
    AliceBalance + BobBalance + PendingBalance = 10

=============================================================================
\* Modification History
\* Last modified Sat Sep 25 14:34:50 CEST 2021 by matthias
\* Created Mon Nov 30 16:13:00 CET 2020 by matthias
