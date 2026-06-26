@date{2026-05-30}
@title{用 Prover9 找等式證明}

@p{有些「單一公理」的代數 presentation，要從該公理推回一般的群律會極其困難 -- 比如 @mention{group-ZXNB} 裡 @code{Div→Group} 需要證明 @m{\text{/-trans} : (a/c)/(b/c) = a/b}，但我們手上卻只有一個等式}
@mm{x / (((x / x) / y / z) / (((x / x) / x) / z)) = y}
@p{這表示手算很難直接湊出來。不過我們可以靠自動定理證明器 @external["https://www.mcs.anl.gov/research/projects/AR/otter/"]{OTTER}（及其後繼者 @external["https://prover9.org/manual-2026/"]{Prover9}）找出來}

@p{這裡記錄實際流程：先讓 Prover9 找出論證骨架，再逐條把它轉寫成 Agda 的等式推理。Prover9 能告訴我們「哪些中繼引理、用什麼順序、由誰推出誰」，剩下的就只是無聊的轉譯工作}

@tr/card{
  @title{安裝}

  @p{macOS 上可以用 Homebrew，這會一併裝上找反例用的 @code{mace4}：}
  @pre{
  brew install prover9
  }
}

@tr/card{
  @title{把問題寫成輸入檔}

  @p{Prover9 是一階等式邏輯的證明器。用 @code{op(...)} 宣告二元運算，公理要寫成 @code{assumptions}，要證的目標放進 @code{goals}（Prover9 實際上是去否證目標的反例）。以 Higman–Neumann 單一除法公理證 @code{/-trans} 為例，存成 @code{trans.in}：}
  @pre{
  op(400, infix, "/").

  formulas(assumptions).
    % Higman–Neumann
    x / ((((x / x) / y) / z) / (((x / x) / x) / z)) = y.
  end_of_list.

  formulas(goals).
    (a / c) / (b / c) = a / b.
  end_of_list.
  }

  @p{接著跑，看有沒有證出來，並把證明物件抓出來：}
  @pre{
  prover9 -f trans.in > trans.out
  grep "THEOREM PROVED" trans.out
  sed -n '/=* PROOF =*/,/=* end of proof =*/p' trans.out
  }

  @p{可以用 @code{assign(max_seconds, 30).} 設搜尋時限；找反例（證明某式「不」成立）則改用 @code{mace4 -f model.in}}
}

@tr/card{
  @title{把長證明拆成「好轉寫」的小引理}

  @p{如果嘗試直接證 @code{/-trans} 會得到一條約 30 步、項非常巨大的 paramodulation 結果，幾乎沒辦法使用。關鍵技巧是把已經證好的中繼引理當成額外 assumption 餵回去，每一步只讓 Prover9 補幾步，產生的子句就短到能逐條轉寫}

  @p{@mention{group-ZXNB} 做的大致上依序是：}
  @ul{
    @li{@code{RID}：@m{x/(y/y) = x}（右單位）}
    @li{@code{UNIT}：@m{x/x = y/y}（單位唯一）}
    @li{@code{INVL}：@m{(x/x)/((x/x)/y) = y}（逆元對合）}
    @li{@code{CL47}：@m{(x/y)/((z/z)/y) = x}（右消去）}
    @li{@code{CL8}：公理對自己代入得到的橋梁等式}
    @li{@code{FLIP}：@m{(x/x)/(y/z) = z/y}（翻轉）}
    @li{@code{/-trans}：@m{(a/c)/(b/c) = a/b}（master lemma）}
  }
  @p{每證好一條就把它加進下一個輸入檔的 @code{assumptions}，於是「Prover9 證下一條」的搜尋只剩幾步}
}

@tr/card{
  @title{把子句轉寫成 Agda}

  @p{Prover9 證明裡每條子句長這樣：}
  @pre{
  102 x / (y / y) = x.  [para(2(a,1),5(a,1,2,2))]
  }
  @p{方括號是「這條怎麼來的」。@code{para(p,q)} 是把子句 @code{p} 的等式代入並改寫子句 @code{q} 的某個子項；@code{rewrite([k(..)])} 是再用引理 @code{k} 改寫一次。對應到 Agda，一條子句就是一段 @code{_＝⟨_⟩_} 鏈：@code{para} 是代入特定值後套用某條等式，@code{rewrite} 則是 @code{ap (λ w → …) (lemma …)} 改寫子項}

  @p{看懂 @code{para} 裡的位置標記很有幫助：@code{7(a,1,1)} 表示「子句 7、等式左邊（@code{1}）、它的第一個引數（@code{1}）」。把位置對上要改寫的子項，就能還原 Prover9 用的代入，再照子句的相依順序逐條寫成 Agda，最後用 @code{agda} 檢查通過即可}
}
