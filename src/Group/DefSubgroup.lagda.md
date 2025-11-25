```
module Group.DefSubgroup where

open import MLTT.Spartan
open import MLTT.Universes
open import UF.Base
open import UF.Sets-Properties

open import Group.Def
open import Group.DefHom
```

子群的定義是，如果存在一個 inclusion 函數 $i : H \to G$ 是一個 group homomorphism，那 $H$ 是 $G$ 的子群。

```
IsSubgroup : {𝓤 𝓥 : Universe} (H G : 𝓤 ̇) {{_ : Group H}} {{_ : Group G}} → 𝓤 ̇
IsSubgroup H G = Sigma (H → G) λ i → left-cancellable i × IsGroupHomomorphism H G i
```
