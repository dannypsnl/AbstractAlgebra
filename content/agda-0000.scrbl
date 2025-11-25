@title{Agda 小知識}

@p{在我們開始之前需要知道怎麼閱讀 agda 的證明，我使用的是由 Martin Escardo 維護的 @external["https://github.com/martinescardo/TypeTopology"]{TypeTopology} 程式庫，下面經常會用到的是等式證明，寫成形式}

@pre{
A ＝⟨ B ⟩ C ∎
}

@p{這段程式的意思是，@m{A = C}，因為 @m{B}。而每個寫好的證明，都可由其他程式引用，比如}

@pre{
propopsition-4 : {G H : 𝓤 ̇} {{∈G : Group G}} {{∈H : Group H}}
  → (φ : G → H)
  → IsGroupHomomorphism G H φ
  → φ e ＝ e
}

@p{就可以引用}

@pre{
φ e ＝⟨ propopsition-4 φ is-hom ⟩
e ∎
}

@p{這就是說 @m{\varphi(e_G) = e_H}，因為前面證明過的事實 @code{propopsition-4 φ is-hom}。}
