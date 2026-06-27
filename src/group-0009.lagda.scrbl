@title{Subgroup equivalent condition}
@taxon{Proposition}

@agda|{
module group-0009 where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import UF.Sets

open import group-0000
open Group {{...}}
open import group-0002
open import group-0004
open import group-0007
}|

@p{這個命題說 H 是 G 的 subgroup 等價於說}

@p{@m{H} 是 @m{G} 的非空子集合，且}

@mm{
a \bullet b^{-1} \in H
}

@p{下面只證明這個條件可以推出}

@ol{
  @li{@m{H} 是一個群}
  @li{@m{H} 是 @m{G} 的子群}
}

@p{因為反過來非常明顯：一個群本身當然是封閉的。}

@blockquote{跟之前一樣，子集合寫成 inclusion 函數}

@agda|{
proposition-7 : {G H : 𝓤 ̇} {{∈G : Group G}}
  → (i : H → G)
  → left-cancellable i
  → is-set H
}|

@p{怎麼表達 @code{H} 不是空集呢？只要說存在一個元素就好}

@agda|{
  → (h : H)
}|

@blockquote{@code{∀ (a b : G) → Σ y ꞉ H , a ∙ b ⁻¹ ＝ i y} 這整個型別要這樣解讀「對所有 @m{a, b \in G}，存在 @m{y \in H} 使 @m{a \bullet b^{-1} = i(y)}」。這裡是目前第一次用到 @code{Σ}，也就是說 @code{Σ} 當命題時，其實就是用來表達「存在某某某滿足什麼什麼條件」的}

@agda|{
  → (∀ (a b : G) → Σ y ꞉ H , a ∙ b ⁻¹ ＝ i y)
  → Σ is-grp ꞉ Group H , IsSubgroup {𝓤} H G {{is-grp}}
proposition-7 {𝓤}{G}{H} {{∈G}} i inclusion H-is-set h cond = H-is-group , i , inclusion , is-hom
  where
}|

@blockquote{接下來的證明很大的複雜性都在 @code{H} 是群這點上，尤其是因為把 @code{cond} 的類型定義成存在 @code{y ∈ H} 映射到 @code{a ∙ b ⁻¹} 這點上，會讓接下來很多簡單的東西都藏在定義後面。其實如果可以，技巧上最好是以 @code{G} 為類型，滿足某種條件的元素，而不是真的用另一個型別 @code{H}，事情會簡單很多}

@p{這裡先定義一些工具，像 @code{I} 就在說 @code{H} 一定有一個元素可以當單位元，也就是採用前面 inhabited 那個 @code{h : H} 然後取 @code{i h ∙ i h ⁻¹} 為單位元（這邊就是技術細節導致的問題，@code{i h ∙ i h ⁻¹} 的類型是 @code{G} 不能直接用，還需要取一次 @code{pr₁} 才是 @code{H} 的 term）}

@agda|{
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
}|

@p{@code{H} 可以用上面定義的工具滿足群的條件}

@agda|{
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
}|

@p{證明的最後一個部分是推論出這樣的 inclusion map 一定是 group homomorphism}

@agda|{
  is-hom : IsGroupHomomorphism H G {{H-is-group}} i
  is-hom x y =
    i (II x y .pr₁) ＝⟨ sym (II x y .pr₂) ⟩
    i x ∙ i y ⁻¹ ⁻¹ ＝⟨ ap (i x ∙_) (inv-inv (i y)) ⟩
    i x ∙ i y ∎
}|

@p{這裡來嘗試第二種編碼方式證明同樣的命題}

@ol{
  @li{用 @code{∈H : G → 𝓤 ̇ } 編碼了屬於 @code{H} 集合這個前提}
  @li{規定 @code{∈H} 是 proposition（沒錯，在 HoTT 裡你同樣能問一個類型是不是一個命題）}
  @li{inhabited @code{h : G} 且 @code{h ∈H} 表示了 @code{H} 不是空集合}
}

@blockquote{下面會反覆使用的技術是 @code{to-Σ-＝}，這樣就會證明一次 @code{G} 中元素在屬於 @code{H} 時的等式，隨後要處理一個 transport 問題，但因為上面第二個條件（@code{∈H} 是 proposition），使得這個證明是完全由 Agda 可以自動合成的}

@agda|{
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Base

proposition-7' : {G : 𝓤 ̇ } {{∈G : Group G}}
  → (_∈H : G → 𝓤 ̇ )
  → (∀ (a : G) → is-prop (a ∈H))
  → (∀ (a b : G) → a ∙ b ⁻¹ ∈H)
  → (h : G)
  → h ∈H
  → Σ is-grp ꞉ Group (Σ x ꞉ G , x ∈H) , IsSubgroup {𝓤} (Σ x ꞉ G , x ∈H) G {{is-grp}}
proposition-7' {𝓤}{G}{{∈G}} _∈H ∈H-is-prop cond h h∈H = H-is-grp , is-subgroup
  where
  inv-inv : (a : G) → a ⁻¹ ⁻¹ ＝ a
  inv-inv a = proposition-2 F S
    where
    F : a ⁻¹ ∙ a ⁻¹ ⁻¹ ＝ e
    F = cancel .pr₂
    S : a ⁻¹ ∙ a ＝ e
    S = cancel .pr₁

  H-is-grp : Group (Σ x ꞉ G , x ∈H)
  H-is-grp .size = subsets-of-sets-are-sets G _∈H (Group.size ∈G) λ {x = x₁} → ∈H-is-prop x₁
  H-is-grp ._∙_ (a , a∈H) (b , b∈H) = a ∙ b ⁻¹ ⁻¹ , cond a (b ⁻¹)
  H-is-grp .∙-assoc (a , a∈H) (b , b∈H) (c , c∈H) = to-Σ-＝ (elem , ∈H-is-prop (pr₁ ((H-is-grp Group.∙ (a , a∈H)) ((H-is-grp Group.∙ (b , b∈H)) (c , c∈H)))) (transport _∈H elem (pr₂ ((H-is-grp Group.∙ (H-is-grp Group.∙ (a , a∈H)) (b , b∈H)) (c , c∈H)))) (pr₂ ((H-is-grp Group.∙ (a , a∈H)) ((H-is-grp Group.∙ (b , b∈H)) (c , c∈H)))))
    where
    elem : (a ∙ b ⁻¹ ⁻¹) ∙ c ⁻¹ ⁻¹ ＝ a ∙ (b ∙ c ⁻¹ ⁻¹) ⁻¹ ⁻¹
    elem =
      (a ∙ b ⁻¹ ⁻¹) ∙ c ⁻¹ ⁻¹ ＝⟨ ∙-assoc a (b ⁻¹ ⁻¹) (c ⁻¹ ⁻¹) ⟩
      a ∙ (b ⁻¹ ⁻¹ ∙ c ⁻¹ ⁻¹) ＝⟨ ap (λ b → a ∙ (b ∙ c ⁻¹ ⁻¹)) (inv-inv b) ⟩
      a ∙ (b ∙ c ⁻¹ ⁻¹)       ＝⟨ ap (a ∙_) (sym (inv-inv (b ∙ c ⁻¹ ⁻¹))) ⟩
      a ∙ (b ∙ c ⁻¹ ⁻¹) ⁻¹ ⁻¹ ∎
  H-is-grp .e = (h ∙ h ⁻¹) , cond h h
  H-is-grp .neu-l (x , x∈H) = to-Σ-＝ (elem , ∈H-is-prop x (transport _∈H elem (pr₂ ((H-is-grp Group.∙ H-is-grp .Group.e) (x , x∈H)))) x∈H)
    where
    elem : (h ∙ h ⁻¹) ∙ x ⁻¹ ⁻¹ ＝ x
    elem =
      (h ∙ h ⁻¹) ∙ x ⁻¹ ⁻¹ ＝⟨ ap (_∙ (x ⁻¹) ⁻¹) (∈G .cancel .pr₂) ⟩
      e ∙ x ⁻¹ ⁻¹          ＝⟨ neu-l (x ⁻¹ ⁻¹) ⟩
      x ⁻¹ ⁻¹              ＝⟨ inv-inv x ⟩
      x ∎
  H-is-grp .neu-r (x , x∈H) = to-Σ-＝ (elem , ∈H-is-prop x (transport _∈H elem (pr₂ ((H-is-grp Group.∙ (x , x∈H)) (H-is-grp .Group.e)))) x∈H)
    where
    elem : x ∙ (h ∙ h ⁻¹) ⁻¹ ⁻¹ ＝ x
    elem =
      x ∙ (h ∙ h ⁻¹) ⁻¹ ⁻¹ ＝⟨ ap (x ∙_) (inv-inv (h ∙ h ⁻¹)) ⟩
      x ∙ (h ∙ h ⁻¹)       ＝⟨ ap (x ∙_) (∈G .cancel .pr₂) ⟩
      x ∙ e                ＝⟨ neu-r x ⟩
      x ∎
  H-is-grp ._⁻¹ (x , x∈H) = (h ∙ h ⁻¹) ∙ x ⁻¹ , cond (h ∙ h ⁻¹) x
  H-is-grp .cancel {x} =
    to-Σ-＝ (cL , ∈H-is-prop (pr₁ (Group.e H-is-grp))
      (transport _∈H cL
       (pr₂ ((H-is-grp Group.∙ (H-is-grp Group.⁻¹) x) x)))
      (pr₂ (Group.e H-is-grp))) ,
    to-Σ-＝ (cR , ∈H-is-prop (pr₁ (Group.e H-is-grp))
      (transport _∈H cR
       (pr₂ ((H-is-grp Group.∙ x) ((H-is-grp Group.⁻¹) x))))
      (pr₂ (Group.e H-is-grp)))
    where
    k = x .pr₁
    cL : (h ∙ h ⁻¹ ∙ k ⁻¹) ∙ k ⁻¹ ⁻¹ ＝ h ∙ h ⁻¹
    cL =
      (h ∙ h ⁻¹ ∙ k ⁻¹) ∙ k ⁻¹ ⁻¹ ＝⟨ ap (h ∙ h ⁻¹ ∙ k ⁻¹ ∙_) (inv-inv k) ⟩
      (h ∙ h ⁻¹ ∙ k ⁻¹) ∙ k       ＝⟨ ap (_∙ k) (∙-assoc h (h ⁻¹) (k ⁻¹)) ⟩
      h ∙ (h ⁻¹ ∙ k ⁻¹) ∙ k       ＝⟨ ∙-assoc h (h ⁻¹ ∙ k ⁻¹) k ⟩
      h ∙ ((h ⁻¹ ∙ k ⁻¹) ∙ k)     ＝⟨ ap (h ∙_) (∙-assoc (h ⁻¹) (k ⁻¹) k) ⟩
      h ∙ (h ⁻¹ ∙ (k ⁻¹ ∙ k))     ＝⟨ ap (h ∙_) (ap (h ⁻¹ ∙_) (cancel .pr₁)) ⟩
      h ∙ (h ⁻¹ ∙ e)              ＝⟨ ap (h ∙_) (neu-r (h ⁻¹)) ⟩
      h ∙ h ⁻¹ ∎
    cR : k ∙ (h ∙ h ⁻¹ ∙ k ⁻¹) ⁻¹ ⁻¹ ＝ h ∙ h ⁻¹
    cR =
      k ∙ (h ∙ h ⁻¹ ∙ k ⁻¹) ⁻¹ ⁻¹ ＝⟨ ap (k ∙_) (inv-inv (h ∙ h ⁻¹ ∙ k ⁻¹)) ⟩
      k ∙ (h ∙ h ⁻¹ ∙ k ⁻¹)       ＝⟨ ap (k ∙_) (ap (_∙ k ⁻¹) (cancel .pr₂)) ⟩
      k ∙ (e ∙ k ⁻¹)              ＝⟨ ap (k ∙_) (neu-l (k ⁻¹)) ⟩
      k ∙ k ⁻¹                    ＝⟨ cancel .pr₂ ⟩
      e                           ＝⟨ sym (cancel .pr₂) ⟩
      h ∙ h ⁻¹ ∎

  ι : Σ x ꞉ G , x ∈H → G
  ι (x , _) = x
  is-subgroup : IsSubgroup {𝓤} (Σ x ꞉ G , x ∈H) G {{H-is-grp}} {{∈G}}
  is-subgroup = ι , (inj , is-hom)
    where
    inj : left-cancellable ι
    inj {x}{y} P =
      x ＝⟨ to-Σ-＝ (P , ∈H-is-prop (y .pr₁) (transport _∈H P (pr₂ x)) (y .pr₂)) ⟩
      y ∎

    is-hom : IsGroupHomomorphism (Σ x ꞉ G , x ∈H) G {{H-is-grp}} {{∈G}} ι
    is-hom (x , x∈H) (y , y∈H) =
      ι ((x , x∈H) ∙ᴴ (y , y∈H)) ＝⟨by-definition⟩
      x ∙ y ⁻¹ ⁻¹                ＝⟨ ap (x ∙_) (inv-inv y) ⟩
      x ∙ y                      ＝⟨by-definition⟩
      ι (x , x∈H) ∙ ι (y , y∈H) ∎
      where open Group H-is-grp renaming (_∙_ to _∙ᴴ_) hiding (_⁻¹)
}|
