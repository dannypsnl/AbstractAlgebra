@title{Preserve inverse}
@taxon{Proposition}

@agda|{
module group-0006 where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)

open import group-0000
open Group {{...}}
open import group-0003
open import group-0004
open import group-0005
}|

@p{Group homomorphism 保留反元素，也就是說 @m{\varphi(g^{-1}) = \varphi(g)^{-1}} 對所有 @m{g \in G} 成立。}

@agda|{
proposition-5 : {G H : 𝓤 ̇} {{∈G : Group G}} {{∈H : Group H}}
  → (φ : G → H)
  → IsGroupHomomorphism G H φ
  → (g : G)
  → φ (g ⁻¹) ＝ (φ g) ⁻¹
proposition-5 φ is-hom g = (proposition-3 .pr₁) III
  where
}|

@p{這裡馬上就用到剛剛證明的保留 identity 性質}

@agda|{
  I : φ (g ⁻¹) ∙ φ g ＝ e
  I = φ (g ⁻¹) ∙ φ g ＝⟨ sym (is-hom (g ⁻¹) g) ⟩
      φ (g ⁻¹ ∙ g)   ＝⟨ ap φ (cancel .pr₁) ⟩
      φ e            ＝⟨ proposition-4 φ is-hom ⟩
      e ∎

  II : e ＝ (φ g) ⁻¹ ∙ (φ g)
  II = sym (cancel .pr₁)

  III : φ (g ⁻¹) ∙ φ g ＝ (φ g) ⁻¹ ∙ (φ g)
  III = I then II
}|
