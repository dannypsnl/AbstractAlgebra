@title{負負得正}
@taxon{Proposition}

@agda|{
module ring-0003 where

open import MLTT.Spartan

open import ring-0000
open Ring {{...}}
open import ring-0002
}|

@p{負負得正通常可能在說兩件事。第一，@m{--a = a}，因為 @m{-a} 的反元素是 @m{a} 也可以是 @m{--a}，因此 @m{--a} 一定等於 @m{a}（因為 Ring 的加法部分是一個 commutative group）。}

@agda|{
neg-neg-lemma : {R : 𝓤 ̇ } {{_ : Ring R}} (x : R) → - - x ＝ x
neg-neg-lemma x = ring-cancel-right (I ∙ II ⁻¹)
  where
  I : - - x +ᴿ - x ＝ 0r
  I = (+-comm (- - x) (- x)) ∙ cancel
  II : x +ᴿ - x ＝ 0r
  II = cancel
}|

@p{或是更重要的 @m{-a \times -b = a \times b}，也就是這裡要證明的命題}

@agda|{
neg-lemma-left : {R : 𝓤 ̇ } {{_ : Ring R}} (a b : R) → - a · b ＝ - (a · b)
neg-lemma-left a b = ring-cancel-right (II ∙ I ⁻¹)
  where
  I : (- (a · b)) +ᴿ a · b ＝ 0r
  I = (- (a · b)) +ᴿ a · b ＝⟨ (+-comm (- (a · b)) (a · b)) ∙ cancel ⟩
      0r ∎
  II : (- a · b) +ᴿ a · b ＝ 0r
  II = (- a · b) +ᴿ a · b ＝⟨ distribL ⁻¹ ⟩
      (- a +ᴿ a) · b      ＝⟨ ap (_· b) ((+-comm (- a) a) ∙ cancel) ⟩
      0r · b              ＝⟨ lemma-1 b .pr₂ ⟩
      0r ∎
neg-lemma-right : {R : 𝓤 ̇ } {{_ : Ring R}} (a b : R) → a · - b ＝ - (a · b)
neg-lemma-right a b = ring-cancel-right (II ∙ I ⁻¹)
  where
  I : (- (a · b)) +ᴿ a · b ＝ 0r
  I = (+-comm (- (a · b)) (a · b)) ∙ cancel
  II : (a · - b) +ᴿ a · b ＝ 0r
  II = (a · - b) +ᴿ a · b ＝⟨ distribR ⁻¹ ⟩
      a · (- b +ᴿ b)      ＝⟨ ap (a ·_) ((+-comm (- b) b) ∙ cancel) ⟩
      a · 0r              ＝⟨ lemma-1 a .pr₁ ⟩
      0r ∎

proposition-2 : {R : 𝓤 ̇ } {{_ : Ring R}} → (a b : R) → - a · - b ＝ a · b
proposition-2 {_}{R} a b =
  (- a · - b) ＝⟨ neg-lemma-left a (- b) ⟩
  - (a · - b) ＝⟨ ap -_ (neg-lemma-right a b) ⟩
  - - (a · b) ＝⟨ neg-neg-lemma (a · b) ⟩
  a · b ∎
}|
