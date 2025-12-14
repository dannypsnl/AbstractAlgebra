```
module Group.DefKer where

open import MLTT.Spartan

open import group-0000
open Group {{...}}
open import Group.DefHom
```

一個 Kernel 是指一個 group homomorphism 的 domain 的子集裡面，那些 maps 到 codomain 的 identity 的元素，所以這裡定義成

```
Ker : {𝓤 : Universe} (H G : 𝓤 ̇) {{_ : Group H}} {{_ : Group G}} (i : H → G) → IsGroupHomomorphism H G i → 𝓤 ̇
Ker H G i _ = Σ h ꞉ H , i h ＝ e
```
