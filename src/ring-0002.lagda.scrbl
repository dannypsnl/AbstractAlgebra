@title{Multiply 0 is 0}
@taxon{Lemma}

@agda|{
module ring-0002 where

open import MLTT.Spartan

open import ring-0000
open Ring {{...}}
}|

@agda|{
lemma-1 : {R : 𝓤 ̇ } {{_ : Ring R}} → (r : R) → (r · 0r ＝ 0r) × (0r · r ＝ 0r)
lemma-1 r = (ring-cancel-right I ⁻¹) , (ring-cancel-right II ⁻¹)
  where
  I : 0r +ᴿ r · 0r ＝ r · 0r +ᴿ r · 0r
  I =
    0r +ᴿ r · 0r   ＝⟨ +-neuL (r · 0r) ⟩
    r · 0r         ＝⟨ ap (r ·_) (+-neuL 0r ⁻¹) ⟩
    r · (0r +ᴿ 0r) ＝⟨ distribR ⟩
    r · 0r +ᴿ r · 0r ∎

  II : 0r +ᴿ 0r · r ＝ 0r · r +ᴿ 0r · r
  II =
    0r +ᴿ 0r · r   ＝⟨ +-neuL (0r · r) ⟩
    0r · r         ＝⟨ ap (_· r) (+-neuL 0r ⁻¹) ⟩
    (0r +ᴿ 0r) · r ＝⟨ distribL ⟩
    0r · r +ᴿ 0r · r ∎
}|
