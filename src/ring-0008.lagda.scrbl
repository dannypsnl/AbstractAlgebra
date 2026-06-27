@title{An element is a (left) unit if and only if (left) action has a section}
@taxon{Proposition}

@agda|{
module ring-0008 where

open import MLTT.Spartan
open import UF.Retracts

open import ring-0000
open Ring {{...}}
open import ring-0006
open import ring-0007
}|

@agda|{
proposition-4 : {R : 𝓤 ̇ } {{_ : Ring R}} → (u : R) → is-left-unit u ↔ has-section (left-action u)
proposition-4 {_} {R} u = if , only-if
  where
  if : is-left-unit u → has-section (left-action u)
  if (v , mul-to-one) = left-action v , iso-to-id
    where
    iso-to-id : (r : R) → (left-action u (left-action v r)) ＝ r
    iso-to-id r =
      (left-action u (left-action v r)) ＝⟨by-definition⟩
      u · (v · r)                       ＝⟨ ·-assoc u v r ⁻¹ ⟩
      (u · v) · r                       ＝⟨ ap (_· r) mul-to-one ⟩
      1r · r                            ＝⟨ ·-neuL r ⟩
      r ∎

  only-if : has-section (left-action u) → is-left-unit u
  only-if (sec , to-id) = sec 1r , to-id 1r
}|
