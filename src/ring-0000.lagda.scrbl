@title{環 Ring}
@taxon{Definition}

@agda|{
module ring-0000 where

open import MLTT.Spartan
open import UF.Sets
}|

@agda|{
record Ring (R : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    size : is-set R

    _+ᴿ_ : R → R → R
    +-assoc : associative _+ᴿ_
    +-comm : commutative _+ᴿ_

    0r : R
    +-neuL : left-neutral 0r _+ᴿ_
    +-neuR : right-neutral 0r _+ᴿ_

    -_ : R → R
    cancel : {x : R} → (x +ᴿ - x ＝ 0r)

    _·_ : R → R → R
    ·-assoc : associative _·_

    1r : R
    ·-neuL : left-neutral 1r _·_
    ·-neuR : right-neutral 1r _·_

    distribL : {r s t : R} → (r +ᴿ s) · t ＝ (r · t) +ᴿ (s · t)
    distribR : {r s t : R} → t · (r +ᴿ s) ＝ (t · r) +ᴿ (t · s)

  infixl 30 _+ᴿ_
  infixl 41 _·_
  infixl 50 -_
}|

@p{下面這個命題是因為 @m{(R, \oplus, 0_R)} 也可以看成一個 commutative group，因此也可以取消共相加的元素來得到結果。其實就是「若 @m{x + 2 = y + 2} 則 @m{x = y}」}

@agda|{
open Ring {{...}}
ring-cancel-right : {R : 𝓤 ̇ } → {{_ : Ring R}} {r s t : R} → s +ᴿ r ＝ t +ᴿ r → s ＝ t
ring-cancel-right {R}{_} {r}{s}{t} fact =
  s               ＝⟨ +-neuR s ⁻¹ ⟩
  s +ᴿ 0r         ＝⟨ ap (s +ᴿ_) (cancel ⁻¹) ⟩
  s +ᴿ (r +ᴿ - r) ＝⟨ +-assoc s r (- r) ⁻¹ ⟩
  s +ᴿ r +ᴿ - r   ＝⟨ ap (_+ᴿ - r) fact ⟩
  t +ᴿ r +ᴿ - r   ＝⟨ +-assoc t r (- r) ⟩
  t +ᴿ (r +ᴿ - r) ＝⟨ ap (t +ᴿ_) cancel ⟩
  t +ᴿ 0r         ＝⟨ +-neuR t ⟩
  t ∎
}|
