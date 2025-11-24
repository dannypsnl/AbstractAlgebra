```
module Group.DefHom where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties

open import Group.Def
```

我們先看 group homomorphism 的定義，基本上它的意思是，對所有 $a,b \in G$

$$
\varphi(a \bullet b) = \varphi(a) \bullet \varphi(b)
$$

成立，那 $\varphi$ 就是一個 group homomorphism

```
open Group {{...}}

IsGroupHomomorphism : (G H : 𝓤 ̇) {{_ : Group G}} {{_ : Group H}} → (φ : G → H) → 𝓤 ̇
IsGroupHomomorphism G H φ = (x y : G) → φ (x ∙ y) ＝ (φ x) ∙ (φ y)
```
