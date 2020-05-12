{-# LANGUAGE CPP, TemplateHaskell #-}
module Data.GADT.Show.TH
    ( DeriveGShow(..)
    ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Data.Dependent.Sum
import Data.Dependent.Sum.TH.Internal
import Data.Functor.Identity
import Data.GADT.Show
import Data.Traversable (for)
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Language.Haskell.TH
import Language.Haskell.TH.Datatype

class DeriveGShow t where
  deriveGShow :: t -> Q [Dec]

instance DeriveGShow Name where
  deriveGShow typeName = do
  typeInfo <- reifyDatatype typeName
  let instTypes = datatypeInstTypes typeInfo
      paramVars = Set.unions [freeTypeVariables t | t <- instTypes]
      instTypes' = case reverse instTypes of
        [] -> fail "deriveGEq: Not enough type parameters"
        (_:xs) -> reverse xs
      instanceHead = AppT (ConT ''GShow) (foldl AppT (ConT typeName) instTypes')
  (clauses, cxt) <- runWriterT (mapM (gshowClause typeName paramVars) (datatypeCons typeInfo))

  return [InstanceD Nothing (datatypeContext typeInfo ++ cxt) instanceHead [gshowFunction clauses]]

instance DeriveGShow Dec where
    deriveGShow = deriveForDec ''GShow $ \typeInfo -> do
      let
        instTypes = datatypeInstTypes typeInfo
        paramVars = Set.unions [freeTypeVariables t | t <- instTypes]
      clauses <- mapM (gshowClause (datatypeName typeInfo) paramVars) (datatypeCons typeInfo)
      return $ gshowFunction clauses

instance DeriveGShow t => DeriveGShow [t] where
    deriveGShow [it] = deriveGShow it
    deriveGShow _ = fail "deriveGShow: [] instance only applies to single-element lists"

instance DeriveGShow t => DeriveGShow (Q t) where
    deriveGShow = (>>= deriveGShow)

gshowFunction :: [Clause] -> Dec
gshowFunction clauses = FunD 'gshowsPrec clauses

isApplicationOf :: Type -> Type -> Bool
isApplicationOf t t' = t == t' || case t' of
  AppT u _ -> isApplicationOf t u
  _ -> False

gshowClause :: Name -> Set Name -> ConstructorInfo -> WriterT [Type] Q Clause
gshowClause typeName paramVars con = do
  let conName  = constructorName con
      argTypes = constructorFields con
      conTyVars = Set.fromList (map tvName (constructorVars con))

  precName <- lift $ newName "prec"
  argNames <- forM argTypes $ \_ -> lift $ newName "x"



  argShowExprs <- forM (zip argNames argTypes) $ \(n,t) -> do
    let useShow = do
          tell [AppT (ConT ''Show) t]
          return [| showsPrec 11 $(varE n) |]
    case t of
      AppT tyFun tyArg -> do
        let useGShow = do
              tell [AppT (ConT ''GShow) tyFun] 
              return [| gshowsPrec 11 $(varE n) |]
        if isApplicationOf (ConT typeName) tyFun
          then return [| gshowsPrec 11 $(varE n) |]
          else do
            v <- lift $ reifyInstancesWithRigids paramVars ''GShow [tyFun]
            case v of
              (_:_) -> useGShow
              _ -> do
                u <- lift $ reifyInstancesWithRigids paramVars ''Show [t]
                case u of
                  (_:_) -> useShow
                  [] -> useGShow
      _ -> useShow

  let precPat = if null argNames
        then wildP
        else varP precName

  lift $ clause [precPat, conP conName (map varP argNames)]
    (normalB (gshowBody (varE precName) conName argShowExprs)) []

showsName name = [| showString $(litE . stringL $ nameBase name) |]

gshowBody :: Q Exp -> Name -> [Q Exp] -> Q Exp
gshowBody prec conName [] = showsName conName
gshowBody prec conName argShowExprs =
  let body = foldr (\e es -> [| $e . $es |]) [| id |] .
               intersperse [| showChar ' ' |] $
                 showsName conName : argShowExprs
  in [| showParen ($prec > 10) $body |]
