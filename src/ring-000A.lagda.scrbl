@title{Multiplication inverse of two sided unit is unique}
@taxon{Proposition}

@agda|{
module ring-000A where

open import MLTT.Spartan

open import ring-0000
open Ring {{...}}
open import ring-0007
}|

@agda|{
proposition-6 : {R : 𝓤 ̇ } {{_ : Ring R}} → (u : R) → (L : is-left-unit u) → (R : is-right-unit u) → L .pr₁ ＝ R .pr₁
proposition-6 u (v , uv=1) (k , ku=1) =
  v           ＝⟨ ·-neuL v ⁻¹ ⟩
  1r · v      ＝⟨ ap (_· v) (ku=1 ⁻¹) ⟩
  k · u · v   ＝⟨ ·-assoc k u v ⟩
  k · (u · v) ＝⟨ ap (k ·_) uv=1 ⟩
  k · 1r      ＝⟨ ·-neuR k ⟩
  k ∎
}|
