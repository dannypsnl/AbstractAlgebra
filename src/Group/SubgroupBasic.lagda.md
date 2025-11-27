```
module Group.SubgroupBasic where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-Properties

open import Group.Def
open Group {{...}}
open import Group.Basic
open import Group.DefHom
open import Group.DefSubgroup
```

## Proposition 6

這個命題是說，對所有群都有一個子群是 trivial group。

要證明之前，我們需要看一下什麼是 trivial group，基本上它就是只有一個估拎拎的 $e$ 元素的集合，那因為只有一個元素，能定義的二元運算子也就只有一個，根據這些我們可以定義 trivial group（`𝟙` 是一個只有單一元素 `⋆` 的型別）

```
trivial-group : Group (𝟙 {𝓤})
trivial-group .size = props-are-sets 𝟙-is-prop
trivial-group ._∙_ = λ _ _ → ⋆
trivial-group .∙-assoc = λ _ _ _ → refl
trivial-group .e = ⋆
trivial-group .neu-l = λ _ → refl
trivial-group .neu-r = λ _ → refl
trivial-group ._⁻¹ = λ _ → ⋆
trivial-group .cancel = refl , refl
```

現在我們可以回到證明，因為 `IsSubgroup` 是一個 Sigma 類型，所以我們需要提出一個 map $\iota$，然後證明這個 map 是 inclusion 而且是 group homomorphism。

```
proposition-6 : {G : 𝓤 ̇} {{∈G : Group G}} {{∈𝟙 : Group 𝟙}}
  → IsSubgroup 𝟙 G
proposition-6 {𝓤} {G} = ι , lc , is-hom
  where
```

這個 map 在數學上常被稱為 canonical map，用來指示「很明顯」會選這個的意思，這在不同數學領域都會有類似的 canonical 的用法，雖然那個「明顯」可能很不一樣。

```
  ι : 𝟙 → G
  ι ⋆ = e
```

它的 inclusion 特性很明顯，甚至都不用到 `p`，因為只有一個元素

```
  lc : left-cancellable ι
  lc p = refl
```

比較複雜的會是滿足 group homomorphism 的部分，大致的思考是利用 $e$ 的一些特性攤開出我們需要的表達式

```
  is-hom : IsGroupHomomorphism 𝟙 G ι
  is-hom ⋆ ⋆ =
    ι (⋆ ∙ ⋆) ＝⟨by-definition⟩
    e         ＝⟨ sym (neu-l e) ⟩
    e ∙ e     ＝⟨by-definition⟩
    (ι ⋆) ∙ (ι ⋆) ∎
```

## Proposition 7

這個命題說 H 是 G 的 subgroup 等價於說

$H$ 是 $G$ 的非空子集合，且

$$
a \bullet b^{-1} \in H
$$

下面只證明這個條件可以推出

1. $H$ 是一個群
2. $H$ 是 $G$ 的子群

因為反過來非常明顯：一個群本身當然是封閉的。

> 跟之前一樣，子集合寫成 inclusion 函數

```
proposition-7 : {G H : 𝓤 ̇} {{∈G : Group G}}
  → (i : H → G)
  → left-cancellable i
  → is-set H
```

怎麼表達 `H` 不是空集呢？只要說存在一個元素就好

```
  → (h : H)
  → (∀ (a b : G) → Σ y ꞉ H , a ∙ b ⁻¹ ＝ i y )
  → Σ is-grp ꞉ Group H , IsSubgroup {𝓤} H G {{is-grp}}
proposition-7 {𝓤}{G}{H} {{∈G}} i inclusion H-is-set h cond = H-is-group , i , inclusion , is-hom
  where
  I : Σ y ꞉ H , i h ∙ i h ⁻¹ ＝ i y
  I = cond (i h) (i h)
  eH : H
  eH = I .pr₁
  prop-eH : i h ∙ i h ⁻¹ ＝ i eH
  prop-eH = I .pr₂
  eH-is-identity : i eH ＝ e
  eH-is-identity = (sym prop-eH) then (cancel .pr₂)

  II : (a b : H) → Σ y ꞉ H , i a ∙ i b ⁻¹ ⁻¹ ＝ i y
  II a b = cond (i a) (i b ⁻¹)

  III : (a : H) → Σ y ꞉ H , i eH ∙ i a ⁻¹ ＝ i y
  III a = cond (i eH) (i a)

  inv-inv : (a : G) → a ⁻¹ ⁻¹ ＝ a
  inv-inv a = proposition-2 F S
    where
    F : a ⁻¹ ∙ a ⁻¹ ⁻¹ ＝ e
    F = cancel .pr₂
    S : a ⁻¹ ∙ a ＝ e
    S = cancel .pr₁

  H-is-group : Group H
  H-is-group .size = H-is-set
  H-is-group ._∙_ a b = II a b .pr₁
  H-is-group .∙-assoc x y z = inclusion VII
    where
    IV : Σ xy ꞉ H , i x ∙ i y ⁻¹ ⁻¹ ＝ i xy
    IV = II x y
    xy = IV .pr₁
    Hxy : i x ∙ i y ⁻¹ ⁻¹ ＝ i xy
    Hxy = IV .pr₂
    V : Σ yz ꞉ H , i y ∙ i z ⁻¹ ⁻¹ ＝ i yz
    V = II y z
    yz = V .pr₁
    Hyz : i y ∙ i z ⁻¹ ⁻¹ ＝ i yz
    Hyz = V .pr₂
    left = II xy z .pr₁
    right = II x yz .pr₁
    help1 = II xy z .pr₂
    help2 = II x yz .pr₂
    mid : i xy ∙ i z ⁻¹ ⁻¹ ＝ i x ∙ i yz ⁻¹ ⁻¹
    mid =
      i xy ∙ i z ⁻¹ ⁻¹        ＝⟨ ap (i xy ∙_) (inv-inv (i z)) ⟩
      i xy ∙ i z              ＝⟨ ap (_∙ i z) (sym Hxy) ⟩
      i x ∙ i y ⁻¹ ⁻¹ ∙ i z   ＝⟨ ap (λ y → i x ∙ y ∙ i z) (inv-inv (i y)) ⟩
      i x ∙ i y ∙ i z         ＝⟨ ap (i x ∙ i y ∙_) (sym (inv-inv (i z))) ⟩
      i x ∙ i y ∙ i z ⁻¹ ⁻¹   ＝⟨ ∙-assoc (i x) (i y) (i z ⁻¹ ⁻¹) ⟩
      i x ∙ (i y ∙ i z ⁻¹ ⁻¹) ＝⟨ ap (i x ∙_) Hyz ⟩
      i x ∙ i yz              ＝⟨ ap (i x ∙_) (sym (inv-inv (i yz))) ⟩
      i x ∙ i yz ⁻¹ ⁻¹ ∎
    VII : i left ＝ i right
    VII = (sym help1) then mid then help2
  H-is-group .e = eH
  H-is-group .neu-l x = inclusion VI
    where
    IV : Σ y ꞉ H , i eH ∙ i x ⁻¹ ⁻¹ ＝ i y
    IV = II eH x
    y = IV .pr₁
    V : i eH ∙ i x ⁻¹ ⁻¹ ＝ i y
    V = IV .pr₂
    VI : i y ＝ i x
    VI =
      i y              ＝⟨ sym V ⟩
      i eH ∙ i x ⁻¹ ⁻¹ ＝⟨ ap (_∙ i x ⁻¹ ⁻¹) eH-is-identity ⟩
      e ∙ i x ⁻¹ ⁻¹    ＝⟨ neu-l (i x ⁻¹ ⁻¹) ⟩
      i x ⁻¹ ⁻¹        ＝⟨ inv-inv (i x) ⟩
      i x ∎
  H-is-group .neu-r x = inclusion VI
    where
    IV : Σ y ꞉ H , i x ∙ i eH ⁻¹ ⁻¹ ＝ i y
    IV = II x eH
    y = IV .pr₁
    V : i x ∙ i eH ⁻¹ ⁻¹ ＝ i y
    V = IV .pr₂
    VI : i y ＝ i x
    VI =
      i y              ＝⟨ sym V ⟩
      i x ∙ i eH ⁻¹ ⁻¹ ＝⟨ ap (i x ∙_) (inv-inv (i eH)) ⟩
      i x ∙ i eH       ＝⟨ ap (i x ∙_) eH-is-identity ⟩
      i x ∙ e          ＝⟨ neu-r (i x) ⟩
      i x ∎
  H-is-group ._⁻¹ x = III x .pr₁
  H-is-group .cancel {x} = left , right
    where
    x' = III x .pr₁
    Hx' : i eH ∙ i x ⁻¹ ＝ i x'
    Hx' = III x .pr₂

    l = II x' x .pr₁
    Hl : i x' ∙ i x ⁻¹ ⁻¹ ＝ i l
    Hl = II x' x .pr₂
    step-left : i x' ∙ i x ⁻¹ ⁻¹ ＝ i eH
    step-left =
      i x' ∙ i x ⁻¹ ⁻¹            ＝⟨ ap (_∙ i x ⁻¹ ⁻¹) (sym Hx') ⟩
      i eH ∙ i x ⁻¹ ∙ i x ⁻¹ ⁻¹   ＝⟨ ∙-assoc (i eH) (i x ⁻¹) (i x ⁻¹ ⁻¹) ⟩
      i eH ∙ (i x ⁻¹ ∙ i x ⁻¹ ⁻¹) ＝⟨ ap (i eH ∙_) (cancel .pr₂) ⟩
      i eH ∙ e                    ＝⟨ neu-r (i eH) ⟩
      i eH ∎

    r = II x x' .pr₁
    Hr : i x ∙ i x' ⁻¹ ⁻¹ ＝ i r
    Hr = II x x' .pr₂
    step-right : i x ∙ i x' ⁻¹ ⁻¹ ＝ i eH
    step-right =
      i x ∙ i x' ⁻¹ ⁻¹      ＝⟨ ap (i x ∙_) (inv-inv (i x')) ⟩
      i x ∙ i x'            ＝⟨ ap (i x ∙_) (sym Hx') ⟩
      i x ∙ (i eH ∙ i x ⁻¹) ＝⟨ ap (i x ∙_) (ap (_∙ i x ⁻¹) eH-is-identity) ⟩
      i x ∙ (e ∙ i x ⁻¹)    ＝⟨ ap (i x ∙_) (neu-l (i x ⁻¹)) ⟩
      i x ∙ i x ⁻¹          ＝⟨ cancel .pr₂ ⟩
      e                     ＝⟨ sym eH-is-identity ⟩
      i eH ∎

    left : (l ＝ eH)
    left = inclusion ((sym Hl) then step-left)
    right : (II x x' .pr₁ ＝ eH)
    right = inclusion ((sym Hr) then step-right)

  is-hom : IsGroupHomomorphism H G {{H-is-group}} i
  is-hom x y =
    i (II x y .pr₁) ＝⟨ sym (II x y .pr₂) ⟩
    i x ∙ i y ⁻¹ ⁻¹ ＝⟨ ap (i x ∙_) (inv-inv (i y)) ⟩
    i x ∙ i y ∎
```
