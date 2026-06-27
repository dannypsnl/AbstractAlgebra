@title{群可以視為一個範疇}
@taxon{Proposition}

@agda|{
open import UF.FunExt
module group-000D (fe : Fun-Ext) where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import Categories.Category fe

open import group-0000
open Group {{...}}
}|

@p{最後我們就用範疇論的常見笑話：群也可以視為一個範疇作為群論的收尾}

@agda|{
group-is-cat : (G : 𝓥 ̇ ) {{_ : Group G}} → precategory 𝓤 𝓥
group-is-cat {𝓥}{𝓤} G = make str axioms
  where
}|

@p{這個範疇只會有一個物件，所以型別是 @code{𝟙}}

@agda|{
  ob = 𝟙
}|

@p{這個範疇的 hom-set 就是群 @code{G}}

@agda|{
  hom : 𝟙 → 𝟙 → 𝓥 ̇
  hom ⋆ ⋆ = G
}|

@p{物件 @m{x} 的 identity hom @m{id_x} 由 @code{G} 的 identity element 提供}

@agda|{
  idn : 𝟙 → G
  idn ⋆ = e
}|

@p{@code{⊚} 表示 hom 的組合，計算上由 @code{G} 的 operation 提供}

@agda|{
  ⊚ : (A B C : 𝟙) → (f g : G) → G
  ⊚ ⋆ ⋆ ⋆ f g = f ∙ g
}|

@p{這些構成了範疇論需要的基本資料}

@agda|{
  str : category-structure 𝓤 𝓥
  str = ob , hom , idn , ⊚
}|

@p{我們需要證明它滿足範疇論所有 hom 的性質}

@ol{
  @li{hom-set 是一個集合}
  @li{@m{id_x} 接 @m{f} 等於 @m{f}}
  @li{@m{f} 接 @m{id_x} 等於 @m{f}}
  @li{associativity 的性質}
}

@p{這些都是直接繼承 @code{G} 自己的性質。}

@agda|{
  axioms : precategory-axioms str
  axioms = (λ A B → size) , (λ A B → neu-l) , (λ A B → neu-r) , final
    where
    final : (A B C D : 𝟙) → (f g h : G) → ⊚ A B D f (⊚ B C D g h) ＝ ⊚ A C D (⊚ A B C f g) h
    final A B C D f g h =
      ⊚ A B D f (⊚ B C D g h) ＝⟨by-definition⟩
      f ∙ (g ∙ h)             ＝⟨ sym (∙-assoc f g h) ⟩
      (f ∙ g) ∙ h             ＝⟨by-definition⟩
      ⊚ A C D (⊚ A B C f g) h ∎
}|
