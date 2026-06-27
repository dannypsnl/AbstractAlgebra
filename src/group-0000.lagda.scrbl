@title{群 Group}
@taxon{Definition}

@agda|{
module group-0000 where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
}|

@p{一個群（group）是由一個非空集合 @m{G} 跟一個二元運算子（binary operation）}

@mm{
\bullet : G \times G \to G
}

@p{構成，且滿足以下條件}

@ol{
  @li{@m{G} 有一個特別的元素叫單位元素（identity 或是 neutral element），用 @m{e} 表示，任何元素 @m{g} 跟它運算都是 @m{g}，也就是 @m{g = g \bullet e = e \bullet g}}
  @li{這個運算子是 associative 的，也就是說 @m{(a \bullet b) \bullet c = a \bullet (b \bullet c)}，所以我們可以安全的寫成 @m{a \bullet b \bullet c}}
  @li{每個元素 @m{g \in G} 都有一個反元素 @m{g^{-1} \in G}，滿足以下等式 @m{g \bullet g^{-1} = g^{-1} \bullet g = e}}
}

@p{我們把這些條件匯總，就寫成了下面的定義}

@agda|{
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
}|
