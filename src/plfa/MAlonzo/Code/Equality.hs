{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

name6 = "Equality._≡_"
d6 a0 a1 a2 = ()
data T6 = C12
name20 = "Equality.sym"
d20 :: () -> AgdaAny -> AgdaAny -> T6 -> T6
d20 = erased
name30 = "Equality.trans"
d30 :: () -> AgdaAny -> AgdaAny -> AgdaAny -> T6 -> T6 -> T6
d30 = erased
name42 = "Equality.cong"
d42 ::
  () -> () -> AgdaAny -> AgdaAny -> (AgdaAny -> AgdaAny) -> T6 -> T6
d42 = erased
name62 = "Equality.cong₂"
d62 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> T6 -> T6 -> T6
d62 = erased
name76 = "Equality.cong-app"
d76 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T6 -> AgdaAny -> T6
d76 = erased
name86 = "Equality.subst"
d86 ::
  () ->
  AgdaAny -> AgdaAny -> (AgdaAny -> ()) -> T6 -> AgdaAny -> AgdaAny
d86 v0 v1 v2 v3 v4 v5 = du86 v5
du86 :: AgdaAny -> AgdaAny
du86 v0 = coe v0
name100 = "Equality.≡-Reasoning.begin_"
d100 :: T6 -> T6
d100 = erased
name108 = "Equality.≡-Reasoning._≡⟨⟩_"
d108 :: T6 -> T6
d108 = erased
name120 = "Equality.≡-Reasoning._≡⟨_⟩_"
d120 :: () -> AgdaAny -> AgdaAny -> AgdaAny -> T6 -> T6 -> T6
d120 = erased
name130 = "Equality.≡-Reasoning._∎"
d130 :: () -> AgdaAny -> T6
d130 = erased
