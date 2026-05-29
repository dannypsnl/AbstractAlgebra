@date{2026-05-30}
@title{代數理論的 presentation}

@p{一個代數理論的 presentation 是一個由可列舉的 variables 給定的集合描述的代數理論，其 terms 遞迴定義成：}

@ol{
  @li{所有 variables 都是 terms}
  @li{在所有 @m{n \in \mathbb{N}} 的 @m{\alpha \in \mathcal{O}_n}，若 @m{t_1, \dots, t_n} 是 terms，那 @m{\alpha(t_1, \dots, t_n)} 也是 term}
}

@p{@m{\mathcal{O}_n} 表示的是 n-ary operators。並且有一系列 axioms，每個 axiom 是由兩個 terms 構成的等式 @m{t_1 = t_2}。}

@p{這個描述當然非常的抽象，以至於難以理解，因此我們就來看看幾個不同的 presentation 以求理解這個定義。群理論可以有很多種 presentation，差別在於各自挑了哪些 operators 跟 axioms；下面兩個都跟 group 等價（或幾乎等價）。}

@transclude{group-DCHP}
@transclude{group-ZXNB}
