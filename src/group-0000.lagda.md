```agda
module group-0000 where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
```

一個群（group）是由一個非空集合 $G$ 跟一個二元運算子（binary operation）

$$
\bullet : G \times G \to G
$$

構成，且滿足以下條件

1. $G$ 有一個特別的元素叫單位元素（identity 或是 neutral element），用 $e$ 表示，任何元素 $g$ 跟它運算都是 $g$，也就是 $g = g \bullet e = e \bullet g$
2. 這個運算子是 associative 的，也就是說 $(a \bullet b) \bullet c = a \bullet (b \bullet c)$，所以我們可以安全的寫成 $a \bullet b \bullet c$
3. 每個元素 $g \in G$ 都有一個反元素 $g^{-1} \in G$，滿足以下等式 $g \bullet g^{-1} = g^{-1} \bullet g = e$

我們把這些條件匯總，就寫成了下面的定義

```agda
record Group (G : 𝓤 ̇) : 𝓤 ̇ where
  field
    size : is-set G
    _∙_ : G → G → G
    ∙-assoc : associative _∙_
    e : G
    neu-l : left-neutral e _∙_
    neu-r : right-neutral e _∙_
    _⁻¹ : G → G
    cancel : {x : G} → ((x ⁻¹) ∙ x ＝ e) × (x ∙ (x ⁻¹) ＝ e)

  infix 40 _⁻¹
  infixl 20 _∙_
```
