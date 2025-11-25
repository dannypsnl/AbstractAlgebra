```
module Group.Basic where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties

open import Group.Def
open Group {{...}}
```

現在來看一些命題

## Proposition 1

假設元素 $h \in G$ 是另一個滿足單位元素條件的元素，那 $h = e$。

> 事實上，很酷的事情是甚至不用完全滿足單位元素條件，就如下面的證明所演示的

```
propopsition-1 : {G : 𝓤 ̇} {{_ : Group G}} {h : G} → left-neutral h _∙_ → h ＝ e
propopsition-1 {G}{_} {h} h-is-identity =
  h ＝⟨ sym (neu-r h) ⟩
  h ∙ e ＝⟨ h-is-identity e ⟩
  e ∎
```

這個命題的重點是單位元素是唯一的，所以英文的話你可以用「the」修飾。

## Proposition 2

如果 $h_1$ and $h_2$ 的反元素都是 $g$，那 $h_1 = h_2$

```
propopsition-2 : {G : 𝓤 ̇} {{_ : Group G}} {g h1 h2 : G} → (g ∙ h1 ＝ e) → (g ∙ h2 ＝ e) → h1 ＝ h2
propopsition-2 {G}{_} {g}{h1}{h2} fact1 fact2 =
  h1 ＝⟨ sym (neu-l h1) ⟩
  e ∙ h1 ＝⟨ ap (_∙ h1) (sym (cancel .pr₁)) ⟩
  g ⁻¹ ∙ g ∙ h1 ＝⟨ ∙-assoc (g ⁻¹) g h1 ⟩
  g ⁻¹ ∙ (g ∙ h1) ＝⟨ ap (g ⁻¹ ∙_) fact1 ⟩
  g ⁻¹ ∙ e ＝⟨ ap ((g ⁻¹) ∙_) (sym fact2) ⟩
  g ⁻¹ ∙ (g ∙ h2) ＝⟨ sym (∙-assoc (g ⁻¹) g h2) ⟩
  g ⁻¹ ∙ g ∙ h2 ＝⟨ ap (_∙ h2) (cancel .pr₁) ⟩
  e ∙ h2 ＝⟨ neu-l h2 ⟩
  h2 ∎
```

## Proposition 3

這個命題在說每個元素都可以取消，這是一個非常好用的事實，不過我們先解釋一下它的具體描述

1. 如果 $g \bullet a = h \bullet a$，則 $g = h$
2. 如果 $a \bullet g = a \bullet h$，則 $g = h$

```
propopsition-3 : {G : 𝓤 ̇} {{_ : Group G}} {g h a : G} → (g ∙ a ＝ h ∙ a → g ＝ h) × (a ∙ g ＝ a ∙ h → g ＝ h)
propopsition-3 {G}{_} {g}{h}{a} = I , II
  where
  I : g ∙ a ＝ h ∙ a → g ＝ h
  I fact =
    g ＝⟨ sym (neu-r g) ⟩
    g ∙ e ＝⟨ ap (g ∙_) (sym (cancel .pr₂)) ⟩
    g ∙ (a ∙ a ⁻¹) ＝⟨ sym (∙-assoc g a (a ⁻¹)) ⟩
    g ∙ a ∙ a ⁻¹ ＝⟨ ap (_∙ a ⁻¹) fact ⟩
    h ∙ a ∙ a ⁻¹ ＝⟨ ∙-assoc h a (a ⁻¹) ⟩
    h ∙ (a ∙ a ⁻¹) ＝⟨ ap (h ∙_) (cancel .pr₂) ⟩
    h ∙ e ＝⟨ neu-r h ⟩
    h ∎

  II : a ∙ g ＝ a ∙ h → g ＝ h
  II fact =
    g ＝⟨ sym (neu-l g) ⟩
    e ∙ g ＝⟨ ap (_∙ g) (sym (cancel .pr₁)) ⟩
    a ⁻¹ ∙ a ∙ g ＝⟨ ∙-assoc (a ⁻¹) a g ⟩
    a ⁻¹ ∙ (a ∙ g) ＝⟨ ap (a ⁻¹ ∙_) fact ⟩
    a ⁻¹ ∙ (a ∙ h) ＝⟨ sym (∙-assoc (a ⁻¹) a h) ⟩
    a ⁻¹ ∙ a ∙ h ＝⟨ ap (_∙ h) (cancel .pr₁) ⟩
    e ∙ h ＝⟨ neu-l h ⟩
    h ∎
```
