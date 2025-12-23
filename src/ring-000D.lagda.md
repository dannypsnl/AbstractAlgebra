```agda
open import UF.PropTrunc
module ring-000D (pt : propositional-truncations-exist) where

open import MLTT.Spartan
open import UF.Powerset
open import UF.SubtypeClassifier
open import UF.Subsingletons

open import ring-0000
open Ring {{...}}
open import ring-000B
open import ring-000C

open PropositionalTruncation pt
```

如果 $I$ 跟 $J$ 是 $R$ 的 ideals，那麼

$$
I + J := \{ i + j \mid i \in I, j \in J \}
$$

也是 $R$ 的 ideal。

```
T : {R : 𝓤 ̇ } {{_ : Ring R}} → (I J : 𝓟 R) → (r : R) → 𝓤 ̇
T {_}{R} I J r = Σ i ꞉ R , Σ j ꞉ R , (i ∈ I) × (j ∈ J) × (r ＝ i +ᴿ j)

_+ᴵ_ : {R : 𝓤 ̇ } {{_ : Ring R}} → (I J : 𝓟 R) → 𝓟 R
_+ᴵ_ {_}{R} I J r = ∥ T I J r ∥ , ∥∥-is-prop
```

使用 propositional truncation `∥_∥` 來表示「存在某種分解」，這樣自動就是 proposition。下面是證明

```
proposition-8 : {R : 𝓤 ̇ } {{_ : Ring R}} {I J : 𝓟 R} → IsIdeal I → IsIdeal J → IsIdeal (I +ᴵ J)
proposition-8 {_}{R}{I}{J} I-is-ideal J-is-ideal = main
  where
  open IsIdeal
  main : IsIdeal (I +ᴵ J)
  main .close-+ {i1}{i2} = ∥∥-rec₂ ∥∥-is-prop helper
    where
    helper : T I J i1 → T I J i2 → ∥ T I J (i1 +ᴿ i2) ∥
    helper (a1 , a2 , a1∈I , a2∈J , i=a1+a2) (b1 , b2 , b1∈I , b2∈J , j=b1+b2) = ∣ a1 +ᴿ b1 , a2 +ᴿ b2 , I-is-ideal .close-+ a1∈I b1∈I , J-is-ideal .close-+ a2∈J b2∈J , res ∣
      where
      res : i1 +ᴿ i2 ＝ (a1 +ᴿ b1) +ᴿ (a2 +ᴿ b2)
      res = i1 +ᴿ i2                 ＝⟨ ap (_+ᴿ i2) i=a1+a2 ⟩
            (a1 +ᴿ a2) +ᴿ i2         ＝⟨ ap (a1 +ᴿ a2 +ᴿ_) j=b1+b2 ⟩
            (a1 +ᴿ a2) +ᴿ (b1 +ᴿ b2) ＝⟨ +-assoc (a1 +ᴿ a2) b1 b2 ⁻¹ ⟩
            (a1 +ᴿ a2 +ᴿ b1) +ᴿ b2   ＝⟨ ap (_+ᴿ b2) (+-assoc a1 a2 b1) ⟩
            (a1 +ᴿ (a2 +ᴿ b1)) +ᴿ b2 ＝⟨ ap (λ - → a1 +ᴿ - +ᴿ b2) (+-comm a2 b1) ⟩
            (a1 +ᴿ (b1 +ᴿ a2)) +ᴿ b2 ＝⟨ ap (_+ᴿ b2) (+-assoc a1 b1 a2 ⁻¹) ⟩
            (a1 +ᴿ b1 +ᴿ a2) +ᴿ b2   ＝⟨ +-assoc (a1 +ᴿ b1) a2 b2 ⟩
            (a1 +ᴿ b1) +ᴿ (a2 +ᴿ b2) ∎
  main .close-neg {i} = ∥∥-rec ∥∥-is-prop helper
    where
    helper : T I J i → ∥ T I J (- i) ∥
    helper (a , b , a∈I , b∈J , i=a+b) = ∣ - a , - b , (I-is-ideal .close-neg a∈I , J-is-ideal .close-neg b∈J , res) ∣
      where
      P : ((- a) +ᴿ (- b)) +ᴿ (a +ᴿ b) ＝ 0r
      P = ((- a) +ᴿ (- b)) +ᴿ (a +ᴿ b) ＝⟨ ap (_+ᴿ (a +ᴿ b)) (+-comm (- a) (- b)) ⟩
          ((- b) +ᴿ (- a)) +ᴿ (a +ᴿ b) ＝⟨ +-assoc (- b) (- a) (a +ᴿ b) ⟩
          (- b) +ᴿ ((- a) +ᴿ (a +ᴿ b)) ＝⟨ ap ((- b) +ᴿ_) (+-assoc (- a) a b ⁻¹) ⟩
          (- b) +ᴿ ((- a) +ᴿ a +ᴿ b)   ＝⟨ ap (- b +ᴿ_) (ap (_+ᴿ b) ((+-comm (- a) a) ∙ cancel)) ⟩
          (- b) +ᴿ (0r +ᴿ b)           ＝⟨ ap (- b +ᴿ_) (+-neuL b) ⟩
          (- b) +ᴿ b                   ＝⟨ ((+-comm (- b) b) ∙ cancel) ⟩
          0r ∎
      Q : - (a +ᴿ b) +ᴿ (a +ᴿ b) ＝ 0r
      Q = - (a +ᴿ b) +ᴿ (a +ᴿ b) ＝⟨ +-comm (- (a +ᴿ b)) (a +ᴿ b) ⟩
          (a +ᴿ b) +ᴿ - (a +ᴿ b) ＝⟨ cancel ⟩
          0r ∎
      res : - i ＝ (- a) +ᴿ (- b)
      res =
        - i        ＝⟨ ap -_ i=a+b ⟩
        - (a +ᴿ b) ＝⟨ ring-cancel-right (Q ∙ P ⁻¹) ⟩
        (- a) +ᴿ (- b) ∎
  main .closeL r {i} = ∥∥-rec ∥∥-is-prop helper
    where
    helper : T I J i → ∥ T I J (r · i) ∥
    helper (a , b , a∈I , b∈J , i=a+b) = ∣ r · a , r · b , I-is-ideal .closeL r a∈I , J-is-ideal .closeL r b∈J , res ∣
      where
      res : r · i ＝ r · a +ᴿ r · b
      res = r · i        ＝⟨ ap (r ·_) i=a+b ⟩
            r · (a +ᴿ b) ＝⟨ distribR ⟩
            r · a +ᴿ r · b ∎
  main .closeR r {i} = ∥∥-rec ∥∥-is-prop helper
    where
    helper : T I J i → ∥ T I J (i · r) ∥
    helper (a , b , a∈I , b∈J , i=a+b) = ∣ a · r , b · r , I-is-ideal .closeR r a∈I , J-is-ideal .closeR r b∈J , res ∣
      where
      res : i · r ＝ a · r +ᴿ b · r
      res = i · r        ＝⟨ ap (_· r) i=a+b ⟩
            (a +ᴿ b) · r ＝⟨ distribL ⟩
            a · r +ᴿ b · r ∎
```
