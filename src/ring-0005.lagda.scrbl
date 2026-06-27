@title{An element is not a (left) zero divisor if and only if (left) action is injective}
@taxon{Proposition}

@p{@m{a \in R} 不是 @mention["ring-0004"]{zero divisor} 若且唯若其 left action @m{x \mapsto a x} 是 injective（也就是 @code{left-cancellable}）}

@agda|{
module ring-0005 where

open import MLTT.Spartan

open import ring-0000
open Ring {{...}}
open import ring-0002
open import ring-0003
open import ring-0004
open import ring-0006
}|

@agda|{
proposition-3 : {R : 𝓤 ̇ } {{_ : Ring R}} {a : R} → NonZeroDivisor a ↔ left-cancellable (left-action a)
proposition-3 {_}{R}{a} = if , only-if
  where
  if : NonZeroDivisor a → left-cancellable (left-action a)
  if is-not-zd {x}{y} Ax=Ay = ring-cancel-right (II ∙ III ⁻¹)
    where
    I : left-action a (x +ᴿ - y) ＝ 0r
    I =
      left-action a (x +ᴿ - y) ＝⟨by-definition⟩
      a · (x +ᴿ - y)           ＝⟨ distribR ⟩
      a · x +ᴿ a · - y         ＝⟨ ap (a · x +ᴿ_) (neg-lemma-right a y) ⟩
      a · x +ᴿ - (a · y)       ＝⟨ ap (_+ᴿ - (a · y)) Ax=Ay ⟩
      a · y +ᴿ - (a · y)       ＝⟨ cancel ⟩
      0r ∎
    II : x +ᴿ - y ＝ 0r
    II = is-not-zd (x +ᴿ - y) I
    III : y +ᴿ - y ＝ 0r
    III = cancel
  only-if : left-cancellable (left-action a) → NonZeroDivisor a
  only-if inj b ab=0 = inj I
    where
    I : a · b ＝ a · 0r
    I = left-action a b ＝⟨by-definition⟩
        a · b           ＝⟨ ab=0 ⟩
        0r              ＝⟨ lemma-1 a .pr₁ ⁻¹ ⟩
        a · 0r          ＝⟨by-definition⟩
        left-action a 0r ∎
}|
