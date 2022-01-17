{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Main where

import           Control.Monad          hiding (fmap)
import           Data.Aeson             (ToJSON, FromJSON)
import           Data.List.NonEmpty     (NonEmpty (..))
import           Data.Map               as Map
import           Data.Text              (pack, Text)
import           GHC.Generics           (Generic)
import           Ledger                 hiding (singleton)
import qualified Ledger.Contexts        as V
import qualified Ledger.Constraints     as Constraints
import qualified Ledger.Typed.Scripts   as Scripts
import           Ledger.Value           as Value
import           Ledger.Ada             as Ada
import           Playground.Contract    (IO, ensureKnownCurrencies, printSchemas, stage, printJson)
import           Playground.TH          (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types       (KnownCurrency (..))
import           Plutus.Contract
import qualified PlutusTx
import           PlutusTx.Prelude       hiding (unless)
import qualified Prelude                as H
import           Schema                 (ToSchema)
import           Text.Printf            (printf)
import           Wallet.Emulator.Wallet (Wallet)
import qualified Wallet.Emulator.Wallet as Wallet
import           Plutus.Trace.Emulator  as Emulator hiding (throwError)
import           Wallet.Emulator.Types  as WalletTypes

minLovelace :: Integer 
minLovelace = 2000000

data FundingDatum = FundingDatum 
    { dOwner :: !PaymentPubKeyHash 
    , dValue :: !Integer
    } deriving(H.Show, Generic, ToJSON, FromJSON, ToSchema)

instance Eq FundingDatum where
    {-# INLINABLE (==) #-}
    a == b = (dOwner a == dOwner b) &&
             (dValue a == dValue b)

PlutusTx.unstableMakeIsData ''FundingDatum
PlutusTx.makeLift ''FundingDatum

data Contribute = Contribute    
    { cValue :: !Integer } deriving H.Show

PlutusTx.unstableMakeIsData ''Contribute
PlutusTx.makeLift ''Contribute

data FundingAction = Contrib Contribute | Claim
    deriving H.Show

PlutusTx.unstableMakeIsData ''FundingAction
PlutusTx.makeLift ''FundingAction

data CrowdFunding 
instance Scripts.ValidatorTypes CrowdFunding where
    type instance RedeemerType CrowdFunding = FundingAction
    type instance DatumType CrowdFunding = FundingDatum

{-# INLINABLE mkFundingValidator #-}
mkFundingValidator :: FundingDatum -> FundingAction -> ScriptContext -> Bool
mkFundingValidator datum redeemer sc = case redeemer of
    Contrib Contribute{..} -> cValue >= 2000000
    Claim                  -> (scriptContextTxInfo sc) `V.txSignedBy` unPaymentPubKeyHash (dOwner datum)

typedFundingValidator :: Scripts.TypedValidator CrowdFunding
typedFundingValidator = Scripts.mkTypedValidator @CrowdFunding
        $$(PlutusTx.compile [|| mkFundingValidator ||])
        $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @FundingDatum @FundingAction

fundingValidator :: Validator
fundingValidator = Scripts.validatorScript typedFundingValidator

fundingHash :: Ledger.ValidatorHash
fundingHash = Scripts.validatorHash typedFundingValidator

fundingAddress :: Ledger.Address
fundingAddress = scriptHashAddress fundingHash

type FundingSchema =
        Endpoint "start" ()
    .\/ Endpoint "contrib" Integer
    .\/ Endpoint "claim" ()

start :: AsContractError e => () -> Contract w s e ()
start _ = do
    pkh <- ownPaymentPubKeyHash
    let datum = FundingDatum
                    { dOwner = pkh
                    , dValue = 2000000
                    }
        v = Ada.lovelaceValueOf minLovelace
        tx = Constraints.mustPayToTheScript datum v
    ledgerTx <- submitTxConstraints typedFundingValidator tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @H.String $ printf "Funding started %s" (H.show datum)

contrib :: Integer -> Contract w s Text ()
contrib amount = do
    (oref, o, d@FundingDatum{..}) <- findCampaign
    logInfo @H.String $ printf "Datum %s" (H.show d)
    let contribution = Contribute { cValue = amount }
        value = dValue + amount
        newDatum = d { dValue = value }
        redeemer = Redeemer $ PlutusTx.toBuiltinData $ Contrib contribution

        lookups = Constraints.typedValidatorLookups typedFundingValidator H.<>
                  Constraints.otherScript fundingValidator                H.<>
                  Constraints.unspentOutputs (Map.singleton oref o)
        tx      = Constraints.mustPayToTheScript newDatum (Ada.lovelaceValueOf value) <>
                  Constraints.mustSpendScriptOutput oref redeemer
    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @H.String $ printf "Contributed with: %s" (H.show amount)

claim :: () -> Contract w s Text ()
claim _ = do
    (oref, o, d@FundingDatum{..}) <- findCampaign
    logInfo @H.String $ printf "Datum %s" (H.show d)

    let redeemer = Redeemer $ PlutusTx.toBuiltinData Claim
        lookups  = Constraints.typedValidatorLookups typedFundingValidator H.<>
                   Constraints.otherScript fundingValidator                H.<>
                   Constraints.unspentOutputs (Map.singleton oref o)
        tx       = Constraints.mustPayToPubKey dOwner (Ada.lovelaceValueOf dValue) <>
                   Constraints.mustSpendScriptOutput oref redeemer
    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @H.String $ printf "Claimed: %s" (H.show dValue)

findCampaign :: Contract w s Text (TxOutRef, ChainIndexTxOut, FundingDatum)
findCampaign = do
    utxos <- utxosAt $ scriptHashAddress fundingHash
    case Map.toList utxos of
        [(oref, o)] -> case _ciTxOutDatum o of
            Left _ -> throwError "datum missing"
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing -> throwError "datum has wrong type"
                Just d@FundingDatum{..} -> return (oref, o, d)
        _ -> throwError "UTXO not found"

endpoints :: Contract () FundingSchema Text ()
endpoints = awaitPromise (start' `select` contrib' `select` claim') >> endpoints
  where
    start' = endpoint @"start" start
    contrib' = endpoint @"contrib" contrib
    claim' = endpoint @"claim" claim

mkSchemaDefinitions ''FundingSchema

myTrace :: EmulatorTrace ()
myTrace = do
    h1 <- activateContractWallet (WalletTypes.fromWalletNumber . WalletNumber $ 1) endpoints
    h2 <- activateContractWallet (WalletTypes.fromWalletNumber . WalletNumber $ 2) endpoints
    h3 <- activateContractWallet (WalletTypes.fromWalletNumber . WalletNumber $ 3) endpoints
    callEndpoint @"start" h1 ()
    void $ waitUntilSlot 10
    callEndpoint @"contrib" h2 2000000
    void $ waitUntilSlot 10
    callEndpoint @"contrib" h3 4000000
    void $ waitUntilSlot 10
    callEndpoint @"claim" h1 ()
    void $ waitUntilSlot 10

main :: H.IO ()
main = runEmulatorTraceIO myTrace