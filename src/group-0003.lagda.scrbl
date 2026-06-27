@title{Every element can be cancelled}
@taxon{Proposition}

@agda|{
module group-0003 where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)

open import group-0000
open Group {{...}}
}|

@p{這個命題在說每個元素都可以取消，這是一個非常好用的事實，而且完全不必感到陌生，我等一下再解釋這點。我們先來看它的具體描述}

@ol{
  @li{如果 @m{g \bullet a = h \bullet a}，則 @m{g = h}}
  @li{如果 @m{a \bullet g = a \bullet h}，則 @m{g = h}}
}

@agda|{
proposition-3 : {G : 𝓤 ̇} {{_ : Group G}} {g h a : G} → (g ∙ a ＝ h ∙ a → g ＝ h) × (a ∙ g ＝ a ∙ h → g ＝ h)
proposition-3 {G}{_} {g}{h}{a} = I , II
  where
  I : g ∙ a ＝ h ∙ a → g ＝ h
  I fact =
    g              ＝⟨ sym (neu-r g) ⟩
    g ∙ e          ＝⟨ ap (g ∙_) (sym (cancel .pr₂)) ⟩
    g ∙ (a ∙ a ⁻¹) ＝⟨ sym (∙-assoc g a (a ⁻¹)) ⟩
    g ∙ a ∙ a ⁻¹   ＝⟨ ap (_∙ a ⁻¹) fact ⟩
    h ∙ a ∙ a ⁻¹   ＝⟨ ∙-assoc h a (a ⁻¹) ⟩
    h ∙ (a ∙ a ⁻¹) ＝⟨ ap (h ∙_) (cancel .pr₂) ⟩
    h ∙ e          ＝⟨ neu-r h ⟩
    h ∎

  II : a ∙ g ＝ a ∙ h → g ＝ h
  II fact =
    g              ＝⟨ sym (neu-l g) ⟩
    e ∙ g          ＝⟨ ap (_∙ g) (sym (cancel .pr₁)) ⟩
    a ⁻¹ ∙ a ∙ g   ＝⟨ ∙-assoc (a ⁻¹) a g ⟩
    a ⁻¹ ∙ (a ∙ g) ＝⟨ ap (a ⁻¹ ∙_) fact ⟩
    a ⁻¹ ∙ (a ∙ h) ＝⟨ sym (∙-assoc (a ⁻¹) a h) ⟩
    a ⁻¹ ∙ a ∙ h   ＝⟨ ap (_∙ h) (cancel .pr₁) ⟩
    e ∙ h          ＝⟨ neu-l h ⟩
    h ∎
}|

@p{為什麼不必對這個命題感到陌生呢？因為這其實是我們日常也很容易遇到的算術事實：如果 @m{2 x = 2 y} 那 @m{x = y}。}
