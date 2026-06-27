@date{2026-05-29}
@title{Division presentation}

@agda|{
module group-ZXNB where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
open import group-0000
open import group-0002
open Group {{...}}
}|

@p{參考：@external["https://www.mcs.anl.gov/uploads/cels/papers/P901.pdf"]{Single axiom: with and without computers} 中的 1952 年 Higman and Neumann}

@p{Division presentation 只有一個二元運算 @code{_/_}（在標準模型中 @code{x / y = x ∙ y ⁻¹}），
而且等式只有一條}

@agda|{
record DivGroup (A : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    _/_     : A → A → A
    /-Higman-Neumann : ∀ x y z → x / (((x / x) / y / z) / (((x / x) / x) / z)) ＝ y
  infixl 20 _/_

Group→DivGroup : {G : 𝓤 ̇ } → {{Group G}} → DivGroup G
Group→DivGroup {𝓤} {G} ⦃ ∈G ⦄ .DivGroup._/_ = λ x y → x ∙ y ⁻¹
Group→DivGroup {𝓤} {G} ⦃ ∈G ⦄ .DivGroup./-Higman-Neumann x y z =
  x / (((x / x) / y / z) / (((x / x) / x) / z)) ＝⟨ ap (λ e → x / ((e / y / z) / (((x / x) / x) / z))) (cancel .pr₂) ⟩
  x / ((e / y / z) / (((x / x) / x) / z))       ＝⟨ ap (λ e₁ → x / ((e / y / z) / ((e₁ / x) / z))) (cancel .pr₂) ⟩
  x / ((e / y / z) / ((e / x) / z))             ＝⟨ ap₂ (λ x₁ x₂ → x / ((x₁ / z) / (x₂ / z))) (neu-l (y ⁻¹)) (neu-l (x ⁻¹)) ⟩
  x / ((y ⁻¹ / z) / (x ⁻¹ / z))                 ＝⟨by-definition⟩
  x ∙ ((y ⁻¹ ∙ z ⁻¹) ∙ (x ⁻¹ ∙ z ⁻¹) ⁻¹) ⁻¹     ＝⟨ ap (λ w → x ∙ ((y ⁻¹ ∙ z ⁻¹) ∙ w) ⁻¹) inv-step ⟩
  x ∙ ((y ⁻¹ ∙ z ⁻¹) ∙ (z ∙ x)) ⁻¹              ＝⟨ ap (λ w → x ∙ w ⁻¹) simp ⟩
  x ∙ (y ⁻¹ ∙ x) ⁻¹                             ＝⟨ ap (x ∙_) (inv-∙ (y ⁻¹) x) ⟩
  x ∙ (x ⁻¹ ∙ y ⁻¹ ⁻¹)                          ＝⟨ ap (λ w → x ∙ (x ⁻¹ ∙ w)) (inv-inv y) ⟩
  x ∙ (x ⁻¹ ∙ y)                                ＝⟨ sym (∙-assoc x (x ⁻¹) y) ⟩
  x ∙ x ⁻¹ ∙ y                                  ＝⟨ ap (_∙ y) (cancel .pr₂) ⟩
  e ∙ y                                         ＝⟨ neu-l y ⟩
  y ∎
  where
  _/_  : G → G → G
  x / y = x ∙ y ⁻¹
  infixl 20 _/_

  inv-inv : ∀ a → a ⁻¹ ⁻¹ ＝ a
  inv-inv a = proposition-2 {g = a ⁻¹} (cancel .pr₂) (cancel .pr₁)

  inv-∙ : ∀ a b → (a ∙ b) ⁻¹ ＝ b ⁻¹ ∙ a ⁻¹
  inv-∙ a b = proposition-2 {g = a ∙ b} (cancel .pr₂)
    ( (a ∙ b) ∙ (b ⁻¹ ∙ a ⁻¹) ＝⟨ ∙-assoc a b (b ⁻¹ ∙ a ⁻¹) ⟩
      a ∙ (b ∙ (b ⁻¹ ∙ a ⁻¹))  ＝⟨ ap (a ∙_) (sym (∙-assoc b (b ⁻¹) (a ⁻¹))) ⟩
      a ∙ (b ∙ b ⁻¹ ∙ a ⁻¹)    ＝⟨ ap (λ w → a ∙ (w ∙ a ⁻¹)) (cancel .pr₂) ⟩
      a ∙ (e ∙ a ⁻¹)           ＝⟨ ap (a ∙_) (neu-l (a ⁻¹)) ⟩
      a ∙ a ⁻¹                 ＝⟨ cancel .pr₂ ⟩
      e ∎ )

  inv-step : (x ⁻¹ ∙ z ⁻¹) ⁻¹ ＝ z ∙ x
  inv-step =
    (x ⁻¹ ∙ z ⁻¹) ⁻¹    ＝⟨ inv-∙ (x ⁻¹) (z ⁻¹) ⟩
    z ⁻¹ ⁻¹ ∙ x ⁻¹ ⁻¹   ＝⟨ ap₂ _∙_ (inv-inv z) (inv-inv x) ⟩
    z ∙ x ∎

  simp : (y ⁻¹ ∙ z ⁻¹) ∙ (z ∙ x) ＝ y ⁻¹ ∙ x
  simp =
    (y ⁻¹ ∙ z ⁻¹) ∙ (z ∙ x)  ＝⟨ sym (∙-assoc (y ⁻¹ ∙ z ⁻¹) z x) ⟩
    y ⁻¹ ∙ z ⁻¹ ∙ z ∙ x      ＝⟨ ap (_∙ x) (∙-assoc (y ⁻¹) (z ⁻¹) z) ⟩
    y ⁻¹ ∙ (z ⁻¹ ∙ z) ∙ x    ＝⟨ ap (λ w → y ⁻¹ ∙ w ∙ x) (cancel .pr₁) ⟩
    y ⁻¹ ∙ e ∙ x             ＝⟨ ap (_∙ x) (neu-r (y ⁻¹)) ⟩
    y ⁻¹ ∙ x ∎
}|

@p{Division presentation 有一個 group presentation 沒有的 model - 空型別 @code{𝟘}。}

@agda|{
empty-DivGroup : DivGroup (𝟘 {𝓤})
empty-DivGroup .DivGroup._/_ = λ ()
empty-DivGroup .DivGroup./-Higman-Neumann = λ ()

no-empty-Group : ¬ Group 𝟘
no-empty-Group G = Group.e G
}|

@p{要把 @code{DivGroup} 重建成 @code{Group}，一個 base point @code{a₀ : A}}

@ol{
  @li{neutral @code{u = a₀ / a₀}}
  @li{乘法定義成 @code{x ∙ y := x / (u / y)}}
  @li{逆元 @code{x ⁻¹ := u / x}}
}

@p{以下用單一 Higman–Neumann 公理重建群。先用 Prover9 找出論證骨架，再轉寫成等式推理}

@agda|{
module Div→Group {A : 𝓤 ̇ } (Aset : is-set A) (a₀ : A) (D : DivGroup A) where
  open DivGroup D
  u : A
  u = a₀ / a₀

  inv : A → A
  inv x = u / x

  mul : A → A → A
  mul x y = x / (u / y)

  i : A → A
  i x = (x / x) / x

  lemB : ∀ x z → x / ((i x / z) / (i x / z)) ＝ x
  lemB x z = /-Higman-Neumann x x z

  RID : ∀ x y → x / (y / y) ＝ x
  RID x y =
    x / (y / y)                 ＝⟨ ap (λ w → x / (w / w)) (sym q) ⟩
    x / (i x / z₁ / (i x / z₁)) ＝⟨ lemB x z₁ ⟩
    x ∎
    where
    z₁ : A
    z₁ = ((i x / i x) / y / x) / (((i x / i x) / i x) / x)
    q : i x / z₁ ＝ y
    q = /-Higman-Neumann (i x) y x

  AX10 : ∀ x y → x / (((x / x) / y) / ((x / x) / x)) ＝ y
  AX10 x y =
    x / (((x / x) / y) / ((x / x) / x))                         ＝⟨ ap₂ (λ a b → x / (a / b)) (sym (RID ((x / x) / y) x)) (sym (RID ((x / x) / x) x)) ⟩
    x / ((((x / x) / y) / (x / x)) / (((x / x) / x) / (x / x))) ＝⟨ /-Higman-Neumann x y (x / x) ⟩
    y ∎

  INVL : ∀ x y → (x / x) / ((x / x) / y) ＝ y
  INVL x y =
    (x / x) / ((x / x) / y)                                                 ＝⟨ ap (λ w → (x / x) / w) (sym shrink) ⟩
    (x / x) / ((((x / x) / (x / x)) / y) / (((x / x) / (x / x)) / (x / x))) ＝⟨ AX10 (x / x) y ⟩
    y ∎
    where
    shrink : (((x / x) / (x / x)) / y) / (((x / x) / (x / x)) / (x / x)) ＝ (x / x) / y
    shrink =
      (((x / x) / (x / x)) / y) / (((x / x) / (x / x)) / (x / x)) ＝⟨ ap (λ w → (w / y) / (w / (x / x))) (RID (x / x) x) ⟩
      ((x / x) / y) / ((x / x) / (x / x))                         ＝⟨ ap (λ w → ((x / x) / y) / w) (RID (x / x) x) ⟩
      ((x / x) / y) / (x / x)                                     ＝⟨ RID ((x / x) / y) x ⟩
      (x / x) / y ∎

  UNIT : ∀ x v → x / x ＝ v / v
  UNIT x v =
    x / x                                     ＝⟨ ap (x /_) (sym (INVL x x)) ⟩
    x / ((x / x) / ((x / x) / x))             ＝⟨ ap (λ w → x / (w / ((x / x) / x))) (sym (RID (x / x) v)) ⟩
    x / (((x / x) / (v / v)) / ((x / x) / x)) ＝⟨ AX10 x (v / v) ⟩
    v / v ∎

  u-is : (x : A) → x / x ＝ u
  u-is x = UNIT x a₀

  runit : (x : A) → x / u ＝ x
  runit x = RID x a₀

  uu : u / u ＝ u
  uu = RID u a₀

  invinv : (x : A) → u / (u / x) ＝ x
  invinv x = INVL a₀ x

  SAX : ∀ x y z → x / (((u / y) / z) / ((u / x) / z)) ＝ y
  SAX x y z =
    x / (((u / y) / z) / ((u / x) / z))             ＝⟨ ap (λ w → x / ((((w) / y) / z) / (((w) / x) / z))) (sym (u-is x)) ⟩
    x / ((((x / x) / y) / z) / (((x / x) / x) / z)) ＝⟨ /-Higman-Neumann x y z ⟩
    y ∎

  S1 : ∀ y z → u / (((u / y) / z) / (u / z)) ＝ y
  S1 y z =
    u / (((u / y) / z) / (u / z))       ＝⟨ ap (λ w → u / (((u / y) / z) / (w / z))) (sym uu) ⟩
    u / (((u / y) / z) / ((u / u) / z)) ＝⟨ SAX u y z ⟩
    y ∎

  S2 : ∀ w z → u / ((w / z) / (u / z)) ＝ u / w
  S2 w z =
    u / ((w / z) / (u / z))             ＝⟨ ap (λ t → u / (((t) / z) / (u / z))) (sym (invinv w)) ⟩
    u / (((u / (u / w)) / z) / (u / z)) ＝⟨ S1 (u / w) z ⟩
    u / w ∎

  S3 : ∀ w z → (w / z) / (u / z) ＝ w
  S3 w z =
    (w / z) / (u / z)             ＝⟨ sym (invinv ((w / z) / (u / z))) ⟩
    u / (u / ((w / z) / (u / z))) ＝⟨ ap (u /_) (S2 w z) ⟩
    u / (u / w)                   ＝⟨ invinv w ⟩
    w ∎

  CL47 : ∀ x y c → (x / y) / ((c / c) / y) ＝ x
  CL47 x y c =
    (x / y) / ((c / c) / y) ＝⟨ ap (λ w → (x / y) / (w / y)) (u-is c) ⟩
    (x / y) / (u / y)       ＝⟨ S3 x y ⟩
    x ∎

  CL8 : ∀ x y z → (x / x) / y ＝ x / ((y / z) / (((x / x) / x) / z))
  CL8 x y z =
    (x / x) / y                                                 ＝⟨ sym (/-Higman-Neumann x ((x / x) / y) z) ⟩
    x / ((((x / x) / ((x / x) / y)) / z) / (((x / x) / x) / z)) ＝⟨ ap (λ w → x / ((w / z) / (((x / x) / x) / z))) (INVL x y) ⟩
    x / ((y / z) / (((x / x) / x) / z)) ∎

  CL29 : ∀ x y c → (x / x) / y ＝ x / (y / ((c / c) / x))
  CL29 x y c =
    (x / x) / y                                                 ＝⟨ CL8 x y ((c / c) / x) ⟩
    x / ((y / ((c / c) / x)) / (((x / x) / x) / ((c / c) / x))) ＝⟨ ap (λ t → x / ((y / ((c / c) / x)) / t)) (CL47 (x / x) x c) ⟩
    x / ((y / ((c / c) / x)) / (x / x))                         ＝⟨ ap (λ t → x / t) (RID (y / ((c / c) / x)) x) ⟩
    x / (y / ((c / c) / x)) ∎

  CL76 : ∀ x y c → (x / x) / (y / x) ＝ x / y
  CL76 x y c =
    (x / x) / (y / x)             ＝⟨ CL29 x (y / x) c ⟩
    x / ((y / x) / ((c / c) / x)) ＝⟨ ap (λ t → x / t) (CL47 y x c) ⟩
    x / y ∎

  FLIP : ∀ x y z → (x / x) / (y / z) ＝ z / y
  FLIP x y z =
    (x / x) / (y / z) ＝⟨ ap (λ w → w / (y / z)) (UNIT x z) ⟩
    (z / z) / (y / z) ＝⟨ CL76 z y z ⟩
    z / y ∎

  CL18 : ∀ x y z → (x / x) / ((y / y) / z) ＝ z
  CL18 x y z =
    (x / x) / ((y / y) / z) ＝⟨ ap (λ w → (x / x) / (w / z)) (sym (UNIT x y)) ⟩
    (x / x) / ((x / x) / z) ＝⟨ INVL x z ⟩
    z ∎

  CL19 : ∀ x y z → (x / ((y / y) / z)) / z ＝ x
  CL19 x y z =
    (x / ((y / y) / z)) / z                         ＝⟨ ap (λ w → (x / ((y / y) / z)) / w) (sym (INVL y z)) ⟩
    (x / ((y / y) / z)) / ((y / y) / ((y / y) / z)) ＝⟨ CL47 x ((y / y) / z) y ⟩
    x ∎

  CL20 : ∀ x y z c → (x / y) / (z / ((y / c) / (((z / z) / z) / c))) ＝ x
  CL20 x y z c =
    (x / y) / (z / ((y / c) / (((z / z) / z) / c))) ＝⟨ ap (λ w → (x / y) / w) (sym (CL8 z y c)) ⟩
    (x / y) / ((z / z) / y)                         ＝⟨ CL47 x y z ⟩
    x ∎

  CL13 : ∀ x y z c → (x / x) / (y / ((z / c) / (((y / y) / y) / c))) ＝ z
  CL13 x y z c =
    (x / x) / (y / ((z / c) / (((y / y) / y) / c))) ＝⟨ ap (λ w → w / (y / ((z / c) / (((y / y) / y) / c)))) (UNIT x z) ⟩
    (z / z) / (y / ((z / c) / (((y / y) / y) / c))) ＝⟨ CL20 z z y c ⟩
    z ∎

  CL40 : ∀ x y z w → ((x / x) / (((y / y) / z) / w)) / z ＝ w
  CL40 x y z w =
    ((x / x) / (((y / y) / z) / w)) / z ＝⟨ ap (λ t → t / z) (FLIP x ((y / y) / z) w) ⟩
    (w / ((y / y) / z)) / z             ＝⟨ CL19 w y z ⟩
    w ∎

  /-trans : ∀ a b c → (a / c) / (b / c) ＝ a / b
  /-trans a b c =
    (a / c) / (b / c)             ＝⟨ ap (λ t → (a / c) / (t / c)) (sym (CL18 d a b)) ⟩
    (a / c) / (((d / d) / d) / c) ＝⟨ sym I ⟩
    a / b ∎
    where
    d : A
    d = (a / a) / b
    w : A
    w = (a / c) / (((d / d) / d) / c)
    I : a / b ＝ (a / c) / (((d / d) / d) / c)
    I =
      a / b                         ＝⟨ ap (λ t → t / b) (sym (CL13 a d a c)) ⟩
      ((a / a) / (d / w)) / b       ＝⟨ CL40 a a b w ⟩
      (a / c) / (((d / d) / d) / c) ∎

  /-unit : (a b : A) → a / a ＝ b / b
  /-unit = UNIT

  flip : (b c : A) → u / (b / c) ＝ c / b
  flip = FLIP a₀

  produce : Group A
  produce .size = Aset
  produce ._∙_ = mul
  produce .∙-assoc x y z =
    (x / (u / y)) / (u / z)                   ＝⟨ ap (λ w → (x / (u / y)) / w) (sym (I y z)) ⟩
    (x / (u / y)) / (((u / z) / y) / (u / y)) ＝⟨ /-trans x ((u / z) / y) (u / y) ⟩
    x / ((u / z) / y)                         ＝⟨ sym (ap (λ w → x / w) (flip y (u / z))) ⟩
    x / (u / (y / (u / z))) ∎
    where
    I : (y z : A) → ((u / z) / y) / (u / y) ＝ u / z
    I y z =
      ((u / z) / y) / (u / y) ＝⟨ /-trans (u / z) u y ⟩
      (u / z) / u             ＝⟨ runit (u / z) ⟩
      u / z ∎
  produce .e = u
  produce .neu-l x = invinv x
  produce .neu-r x =
    x / (u / u) ＝⟨ ap (λ w → x / w) (u-is u) ⟩
    x / u       ＝⟨ runit x ⟩
    x ∎
  produce Group.⁻¹ = inv
  produce .cancel {x} = (u-is (u / x)) , I
    where
    I : mul x (inv x) ＝ u
    I = x / (u / (u / x)) ＝⟨ ap (λ w → x / w) (invinv x) ⟩
        x / x             ＝⟨ u-is x ⟩
        u ∎
}|
