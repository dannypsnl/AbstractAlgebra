```
module Group.DefKer where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import UF.Equiv

open import Group.Def
open Group {{...}}
open import Group.DefHom
```

```
Ker : {𝓤 : Universe} (H G : 𝓤 ̇) {{_ : Group H}} {{_ : Group G}} (i : H → G) → 𝓤 ̇
Ker H G i = Σ h ꞉ H , i h ＝ e

a : {H G : 𝓤 ̇} {{_ : Group H}} {{_ : Group G}}
  (i : H → G)
  → IsGroupHomomorphism H G i
  → left-cancellable i
  → (Ker H G i) ≃ 𝟙 {𝓤}
a = {!   !}
```
