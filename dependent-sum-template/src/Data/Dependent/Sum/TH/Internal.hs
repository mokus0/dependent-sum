{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
-- | Shared functions for dependent-sum-template
module Data.Dependent.Sum.TH.Internal where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Extras
import Language.Haskell.TH.Datatype.TyVarBndr

classHeadToParams :: Type -> (Name, [Type])
classHeadToParams t = (h, reverse reversedParams)
  where (h, reversedParams) = go t
        go :: Type -> (Name, [Type])
        go t = case t of
          AppT f x ->
            let (h, reversedParams) = classHeadToParams f
            in (h, x : reversedParams)
          _ -> (headOfType t, [])

-- Invoke the deriver for the given class instance.  We assume that the type
-- we're deriving for is always the first typeclass parameter, if there are
-- multiple.
deriveForDec :: Name -> (Q Type -> Q Type) -> ([TyVarBndrSpec] -> [Con] -> Q Dec) -> Dec -> Q [Dec]
deriveForDec className makeClassHead f dec = deriveForDec' className makeClassHead (f . changeTVFlags specifiedSpec) dec

deriveForDec' :: Name -> (Q Type -> Q Type) -> ([TyVarBndrUnit] -> [Con] -> Q Dec) -> Dec -> Q [Dec]
deriveForDec' className _ f (InstanceD overlaps cxt classHead decs) = do
    let (givenClassName, firstParam : _) = classHeadToParams classHead
    when (givenClassName /= className) $
      fail $ "while deriving " ++ show className ++ ": wrong class name in prototype declaration: " ++ show givenClassName
    let dataTypeName = headOfType firstParam
    dataTypeInfo <- reify dataTypeName
    case dataTypeInfo of
        TyConI (DataD dataCxt name bndrs _ cons _) -> do
            dec <- f bndrs cons
            return [InstanceD overlaps cxt classHead [dec]]
        _ -> fail $ "while deriving " ++ show className ++ ": the name of an algebraic data type constructor is required"
deriveForDec' className makeClassHead f (DataD dataCxt name bndrs _ cons _) = return <$> inst
    where
        inst = instanceD (cxt (map return dataCxt)) (makeClassHead $ conT name) [dec]
        dec = f bndrs cons
#if __GLASGOW_HASKELL__ >= 808
deriveForDec' className makeClassHead f (DataInstD dataCxt tvBndrs ty _ cons _) = return <$> inst
#else
deriveForDec' className makeClassHead f (DataInstD dataCxt name tyArgs _ cons _) = return <$> inst
#endif
    where
        inst = instanceD (cxt (map return dataCxt)) clhead [dec]
#if __GLASGOW_HASKELL__ >= 808
        clhead = makeClassHead $ return $ initTy ty
#if __GLASGOW_HASKELL__ >= 900
        bndrs = [PlainTV v x | PlainTV v x <- maybe [] id tvBndrs]
#else
        bndrs = [PlainTV v | PlainTV v <- maybe [] id tvBndrs]
#endif
        initTy (AppT ty _) = ty
#else
        clhead = makeClassHead $ foldl1 appT (map return $ (ConT name : init tyArgs))
        -- TODO: figure out proper number of family parameters vs instance parameters
        bndrs = [PlainTV v | VarT v <- tail tyArgs ]
#endif
        dec = f bndrs cons
