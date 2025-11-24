```
module Group.HomBasic where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties

open import Group.Def
open Group {{...}}
open import Group.Basic
open import Group.DefHom
```

## Proposition 4

Group homomorphism preserves identity element.

```
propopsition-4 : {G H : 𝓤 ̇}
  {{_ : Group G}} {{_ : Group H}}
  → (φ : G → H)
  → IsGroupHomomorphism G H φ
  → φ e ＝ e
propopsition-4 φ is-hom = VI
  where
  I : e ⁻¹ ＝ e
  I = e ⁻¹ ＝⟨ sym (neu-r (e ⁻¹)) ⟩
      e ⁻¹ ∙ e ＝⟨ cancel .pr₁ ⟩
      e ∎

  II : φ e ＝ (φ e) ∙ (φ e)
  II = φ e ＝⟨ ap (λ x → φ x) (sym (cancel .pr₁)) ⟩
       φ (e ⁻¹ ∙ e) ＝⟨ ap (λ x → φ (x ∙ e)) I ⟩
       φ (e ∙ e) ＝⟨ is-hom e e ⟩
       (φ e) ∙ (φ e) ∎

  III : (φ e) ∙ (φ e) ＝ e ∙ (φ e)
  III = (φ e) ∙ (φ e) ＝⟨ sym II ⟩
        φ e ＝⟨ sym (neu-l (φ e)) ⟩
        e ∙ φ e ∎

  VI : (φ e) ＝ e
  VI = (propopsition-3 .pr₁) III
```
