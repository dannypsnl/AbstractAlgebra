@title{If an element is a (left) unit then its (right) action is injective}
@taxon{Proposition}

@agda|{
module ring-0009 where

open import MLTT.Spartan
open import UF.Retracts

open import ring-0000
open Ring {{...}}
open import ring-0006
open import ring-0007
}|

@agda|{
proposition-5 : {R : 𝓤 ̇ } {{_ : Ring R}} → (u : R) → is-left-unit u → left-cancellable (right-action u)
proposition-5 u (v , uv＝1) {x}{y} xu＝yu =
  x           ＝⟨ ·-neuR x ⁻¹ ⟩
  x · 1r      ＝⟨ ap (x ·_) (uv＝1 ⁻¹) ⟩
  x · (u · v) ＝⟨ ·-assoc x u v ⁻¹ ⟩
  x · u · v   ＝⟨ ap (_· v) xu＝yu ⟩
  y · u · v   ＝⟨ ·-assoc y u v ⟩
  y · (u · v) ＝⟨ ap (y ·_) uv＝1 ⟩
  y · 1r      ＝⟨ ·-neuR y ⟩
  y ∎
}|
