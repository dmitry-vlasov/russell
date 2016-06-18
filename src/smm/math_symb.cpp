#include "smm/globals.hpp"
#include "rus/ast.hpp"

namespace mdl { namespace smm {

inline rus::Const make_symb(const char* ascii, const char* unicode, const char* latex) {
	return rus::Const {
		Smm::mod().lex.symbols.toInt(unicode),
		Smm::mod().lex.symbols.toInt(ascii),
		Smm::mod().lex.symbols.toInt(latex)
	};
}

inline uint make_key(const char* key) {
	return Smm::mod().lex.symbols.toInt(key);
}

map<uint, rus::Const> math_symb = {
		{make_key("|-"), make_symb("|-", "⊢", "vdash")},
		{make_key("->"), make_symb("->", "→", "\\rightarrow")},
		{make_key("-."), make_symb("-.", "¬", "\\lnot")},
		{make_key("<->"), make_symb("<->", "↔", "\\leftrightarrow")},
		{make_key("\\/"), make_symb("\\/", "∨", "\\lor")},
		{make_key("/\\"), make_symb("/\\", "∧", "\\land")},
		{make_key("-/\\"), make_symb("-/\\", "⊼", "\\bar{\\wedge}")},
		{make_key("A."), make_symb("A.", "∀", "\\forall")},
		{make_key("E."), make_symb("E.", "∃", "\\exists")},
		{make_key("e."), make_symb("e.", "∈", "\\in")},
		{make_key("E!"), make_symb("E!", "∃!", "\\exists{!}")},
		{make_key("E*"), make_symb("E*", "∃*", "\\exists^{\\ast}")},
		{make_key("{"), make_symb("{", "{", "\\{")},
		{make_key("}"), make_symb("}", "}", "\\}")},
		{make_key("=/="), make_symb("=/=", "≠", "\\ne")},
		{make_key("e/"), make_symb("e/", "∉", "\\notin")},
		{make_key("V"), make_symb("V", "𝐕", "\\rm{V}")},
		{make_key("[_"), make_symb("[_", "[", "[")},
		{make_key("]_"), make_symb("]_", "]", "]")},
		{make_key("C"), make_symb("C", "⊆", "\\subseteq")},
		{make_key("C."), make_symb("C.", "⊂", "\\subset")},
		{make_key("\\"), make_symb("\\", "∖", "\\setminus")},
		{make_key("u."), make_symb("u.", "∪", "\\cup")},
		{make_key("i^i"), make_symb("i^i", "∩", "\\cap")},
		{make_key("(/)"), make_symb("(/)", "∅", "\\emptyset")},
		{make_key("~P"), make_symb("~P", "Pow", "\\cal{P}")},
		{make_key("<."), make_symb("<.", "〈", "\\langle")},
		{make_key(">."), make_symb(">.", "〉", "\\rangle")},
		{make_key("U."), make_symb("U.", "⋃", "\\bigcup")},
		{make_key("|^|"), make_symb("|^|", "⋂", "\\bigcap")},
		{make_key("U_"), make_symb("U_", "⋃_", "\\bigcup")},
		{make_key("|^|_"), make_symb("|^|_", "⋂_", "\\bigcap")},
		{make_key("_E"), make_symb("_E", "𝛜", "\\epsilon")},
		{make_key("_I"), make_symb("_I", "Id", "\\rm{Id}")},
		{make_key("om"), make_symb("om", "ω", "\\omega")},
		{make_key("X."), make_symb("X.", "×", "\\times")},
		{make_key("`'"), make_symb("`'", "⁻¹", "{}^{-1}")},
		{make_key("|`"), make_symb("|`", "↾", "\\upharpoonright")},
		{make_key("\""), make_symb("\"", "\"", "``")},
		{make_key("o."), make_symb("o.", "∘", "\\circ")},
		{make_key("-->"), make_symb("-->", "⟶", "\\longrightarrow")},
		{make_key("-1-1->"), make_symb("-1-1->", "↣", "\\rightarrowtail")},
		{make_key("-onto->"), make_symb("-onto->", "↠", "\\twoheadrightarrow")},
		{make_key("-1-1-onto->"), make_symb("-1-1-onto->", "⤖", "\\rightarrowtail\\twoheadrightarrow")},
		{make_key("X_"), make_symb("X_", "×_", "\\times")},
		{make_key("|->"), make_symb("|->", "↦", "\\times")},
		{make_key("^m"), make_symb("^m", "↑m", "\\uparrow_m")},
		{make_key("^pm"), make_symb("^pm", "↑pm", "\\uparrow_{pm}")},
		{make_key("+o"), make_symb("+o", "+ₒ", "+_o")},
		{make_key(".o"), make_symb(".o", "∙ₒ", "\\cdot_o")},
		{make_key("^o"), make_symb("^o", "↑ₒ", "\\uparrow_o")},
		{make_key("1o"), make_symb("1o", "1ₒ", "1_o")},
		{make_key("2o"), make_symb("2o", "2ₒ", "2_o")},
		{make_key("/."), make_symb("/.", "/", "\\diagup")},
		{make_key("~~"), make_symb("~~", "≈", "\\approx")},
		{make_key("~<_"), make_symb("~<_", "≼", "\\preccurlyeq")},
		{make_key("~<"), make_symb("~<", "≺", "\\prec")},
		{make_key("aleph"), make_symb("aleph", "ℵ", "\\aleph")},
		{make_key("+c"), make_symb("+c", "+𝐜", "+_c")},
		{make_key("R1"), make_symb("R1", "R₁", "R_1")},
		{make_key(".N"), make_symb(".N", "∙N", "\\cdot_{\\cal{N}}")},
		{make_key("<N"), make_symb("<N", "<N", "<_{\\cal{N}}")},
		{make_key("+pQ"), make_symb("+pQ", "+pQ", "+_{p\\cal{Q}}")},
		{make_key(".pQ"), make_symb(".pQ", "∙pQ", "\\cdot_{p\\cal{Q}}")},
		{make_key("Q."), make_symb("Q.", "Q.", "\\cal{Q}")},
		{make_key(".Q"), make_symb(".Q", "∙Q", "\\cdot_{\\cal{Q}}")},
		{make_key("P."), make_symb("P.", "Pos", "\\rm{Pos}")},
		{make_key("1P"), make_symb("1P", "1Pos", "1_{\\rm{Pos}}")},
		{make_key("+P."), make_symb("+P.", "+Pos", "+_{\\rm{Pos}}")},
		{make_key(".P."), make_symb(".P.", "∙Pos", "\\cdot_{\\rm{Pos}}")},
		{make_key("<P"), make_symb("<P", "<Pos", "<_{\\rm{Pos}}")},
		{make_key("+pR"), make_symb("+pR", "+pR", "+_{p\\cal{R}}")},
		{make_key(".pR"), make_symb(".pR", "∙pR", "\\cdot_{p\\cal{R}}")},
		{make_key("-1R"), make_symb("-1R", "-1R", "-1_{p\\cal{R}}")},
		{make_key(".R"), make_symb(".R", "∙R", "\\cdot_{p\\cal{R}}")},
		{make_key("<R"), make_symb("<R", "<R", "<_{p\\cal{R}}")},
		{make_key("<RR"), make_symb("<RR", "<ℝ", "<_{\\mathbb{R}}")},
		{make_key("CC"), make_symb("CC", "ℂ", "\\mathbb{C}")},
		{make_key("RR"), make_symb("RR", "ℝ", "\\mathbb{R}")},
		{make_key("x."), make_symb("x.", "∙", "\\cdot")},
		{make_key("+oo"), make_symb("+oo", "+∞", "+\\infty")},
		{make_key("-oo"), make_symb("-oo", "-∞", "-\\infty")},
		{make_key("RR*"), make_symb("RR*", "ℝ*", "\\mathbb{R}*")},
		{make_key("<_"), make_symb("<_", "≤", "\\le")},
		{make_key("NN"), make_symb("NN", "ℕ", "\\mathbb{N}")},
		{make_key("NN0"), make_symb("NN0", "ℕ₀", "\\mathbb{N}_0")},
		{make_key("ZZ"), make_symb("ZZ", "ℤ", "\\mathbb{Z}")},
		{make_key("QQ"), make_symb("QQ", "ℚ", "\\mathbb{Q}")},
		{make_key("RR+"), make_symb("RR+", "ℝ⁺", "\\mathbb{R}^+")},
		{make_key("sqr"), make_symb("sqr", "√", "\\surd")},
		{make_key("Re"), make_symb("Re", "ℜ", "\\Re")},
		{make_key("Im"), make_symb("Im", "ℑ", "\\Im")},
		{make_key("|_"), make_symb("|_", "⌊", "\\lfloor")},
		{make_key("=="), make_symb("==", "≡", "\\equiv")},
		{make_key("seq1"), make_symb("seq1", "seq₁", "\\rm{seq}_1")},
		{make_key("ZZ>="), make_symb("ZZ>=", "ℤ≥", "\\mathbb{Z}_\\ge")},
		{make_key("seq0"), make_symb("seq0", "seq₀", "\\rm{seq}_0")},
		{make_key("^"), make_symb("^", "↑", "\\uparrow")},
		{make_key("~~>"), make_symb("~~>", "⇝", "\\rightsquigarrow")},
		{make_key("..."), make_symb("...", "...", "\\ldots")},
		{make_key("sum_"), make_symb("sum_", "∑", "\\sigma")},
		{make_key("_e"), make_symb("_e", "ℇ", "\\rm{e}")},
		{make_key("pi"), make_symb("pi", "π", "\\pi")},
		{make_key("-cn->"), make_symb("-cn->", "‒cn→", "\\longrightarrow_{\\rm{cn}}")},
		{make_key("~~>m"), make_symb("~~>m", "⇝m", "\\rightsquigarrow_{\\rm{m}}")},
		{make_key("Id"), make_symb("Id", "Id", "\\rm{Id}")},
		{make_key("^g"), make_symb("^d", "↑g", "\\uparrow_g")},
		{make_key(".s"), make_symb(".s", "∙s", "\\cdot_s")},
		{make_key(".i"), make_symb(".i", "∙i", "\\cdot_i")},
		{make_key("~~>v"), make_symb("~~>v", "⇝v", "\\rightsquigarrow_{\\rm{v}}")},
		{make_key("_|_"), make_symb("_|_", "⊥", "\\perp")},
		{make_key("vH"), make_symb("vH", "vH", "\\vee_\\mathfrak{H}")},
		{make_key("\\/H"), make_symb("\\/H", "\\/H", "\\bigvee_\\mathfrak{H}")},
		{make_key("<_op"), make_symb("<_op", "≤op", "\\le_{\\rm{op}}")},
		{make_key("Lambda"), make_symb("Lambda", "Λ", "\\Lambda")},
		{make_key("<o"), make_symb("<o", "⋖", "\\lessdot")},
		{make_key("1stc"), make_symb("1stc", "1stω", "1^{\\rm{st}}\\omega")},
		{make_key("2ndc"), make_symb("2ndc", "2ndω", "2^{\\rm{nd}}\\omega")},
		{make_key("prod_"), make_symb("prod_", "∏", "\\Pi")},
		{make_key("(+)"), make_symb("(+)", "⊕", "\\oplus")},
		{make_key("~~>t"), make_symb("~~>t", "⇝t", "\\rightsquigarrow_{\\rm{t}}")},
		{make_key("=~ph"), make_symb("=~ph", "=~φ", "\\mbox{$=$\\~{}ph}")},
		{make_key("->.."), make_symb("->..", "⇒", "\\Longrightarrow")}
};

/*
symbol
	ascii |-
	unicode ⊢
	latex \vdash
symbol
	ascii ->
	unicode →
	latex \rightarrow
symbol
	ascii -.
	unicode ¬
	latex \lnot
symbol
	ascii <->
	unicode ↔
	latex \leftrightarrow
symbol
	ascii \/
	unicode ∨
	latex \lor
symbol
	ascii /\
	unicode ∧
	latex \land
symbol
	ascii -/\
	unicode ⊼
	latex \bar{\wedge}
symbol
	ascii A.
	unicode ∀
	latex \forall
symbol
	ascii E.
	unicode ∃
	latex \exists
symbol
	ascii =
	unicode =
	latex =
symbol
	ascii e.
	unicode ∈
	latex \in
symbol
	ascii [
	unicode [
	latex [
symbol
	ascii /
	unicode /
	latex /
symbol
	ascii ]
	unicode ]
	latex ]
symbol
	ascii E!
	unicode ∃!
	latex \exists{!}
symbol
	ascii E*
	unicode ∃*
	latex \exists^{\ast}
symbol
	ascii {
	unicode {
	latex \{
symbol
	ascii |
	unicode |
	latex |
symbol
	ascii }
	unicode }
	latex \}
symbol
	ascii =/=
	unicode ≠
	latex \ne
symbol
	ascii e/
	unicode ∉
	latex \notin
symbol
	ascii _V
	unicode 𝐕
	latex \rm{V}
symbol
	ascii [_
	unicode [
	latex [
symbol
	ascii ]_
	unicode ]
	latex ]
symbol
	ascii C_
	unicode ⊆
	latex \subseteq
symbol
	ascii C.
	unicode ⊂
	latex \subset
symbol
	ascii \
	unicode ∖
	latex \setminus
symbol
	ascii u.
	unicode ∪
	latex \cup
symbol
	ascii i^i
	unicode ∩
	latex \cap
symbol
	ascii (/)
	unicode ∅
	latex \emptyset
symbol
	ascii ,
	unicode ,
	latex ,
symbol
	ascii ~P
	unicode Pow
	latex \cal{P}
symbol
	ascii <.
	unicode 〈
	latex \langle
symbol
	ascii >.
	unicode 〉
	latex \rangle
symbol
	ascii U.
	unicode ⋃
	latex \bigcup
symbol
	ascii |^|
	unicode ⋂
	latex \bigcap
symbol
	ascii U_
	unicode ⋃
	latex \bigcup
symbol
	ascii |^|_
	unicode ⋂
	latex \bigcap
symbol
	ascii _E
	unicode 𝛜
	latex \epsilon
symbol
	ascii _I
	unicode Id
	latex \rm{Id}
symbol
	ascii om
	unicode ω
	latex \omega
symbol
	ascii X.
	unicode ×
	latex \times
symbol
	ascii `'
	unicode ⁻¹
	latex {}^{-1}
symbol
	ascii |`
	unicode ↾
	latex \upharpoonright
symbol
	ascii "
	unicode "
	latex ``
symbol
	ascii o.
	unicode ∘
	latex \circ
symbol
	ascii :
	unicode :
	latex :
symbol
	ascii -->
	unicode ⟶
	latex \longrightarrow
symbol
	ascii -1-1->
	unicode ↣
	latex \rightarrowtail
symbol
	ascii -onto->
	unicode ↠
	latex \twoheadrightarrow
symbol
	ascii -1-1-onto->
	unicode ⤖
	latex \rightarrowtail\twoheadrightarrow
symbol
	ascii `
	unicode `
	latex `
symbol
	ascii X_
	unicode ×_
	latex \times
symbol
	ascii |->
	unicode ↦
	latex \mapsto
symbol
	ascii ^m
	unicode ↑m
	latex \uparrow_m
symbol
	ascii ^pm
	unicode ↑pm
	latex \uparrow_{pm}
symbol
	ascii +o
	unicode +ₒ
	latex +_o
symbol
	ascii .o
	unicode ∙ₒ
	latex \cdot_o
symbol
	ascii ^o
	unicode ↑ₒ
	latex \uparrow_o
symbol
	ascii 1o
	unicode 1ₒ
	latex 1_o
symbol
	ascii 2o
	unicode 2ₒ
	latex 2_o
symbol
	ascii /.
	unicode ∕
	latex \diagup
symbol
	ascii ~~
	unicode ≈
	latex \approx
symbol
	ascii ~<_
	unicode ≼
	latex \preccurlyeq
symbol
	ascii ~<
	unicode ≺
	latex \prec
symbol
	ascii aleph
	unicode ℵ
	latex \aleph
symbol
	ascii +c
	unicode +𝐜
	latex +_c
symbol
	ascii R1
	unicode R₁
	latex R_1
symbol
	ascii .N
	unicode ∙N
	latex \cdot_{\cal{N}}
symbol
	ascii <N
	unicode <N
	latex <_{\cal{N}}
symbol
	ascii +pQ
	unicode +pQ
	latex +_{p\cal{Q}}
symbol
	ascii .pQ
	unicode ∙pQ
	latex \cdot_{p\cal{Q}}
symbol
	ascii Q.
	unicode Q.
	latex \cal{Q}
symbol
	ascii .Q
	unicode ∙Q
	latex \cdot_{\cal{Q}}
symbol
	ascii P.
	unicode Pos
	latex \rm{Pos}
symbol
	ascii 1P
	unicode 1Pos
	latex 1_{\rm{Pos}}
symbol
	ascii +P.
	unicode +Pos
	latex +_{\rm{Pos}}
symbol
	ascii .P.
	unicode ∙Pos
	latex \cdot_{\rm{Pos}}
symbol
	ascii <P
	unicode <Pos
	latex <_{\rm{Pos}}
symbol
	ascii +pR
	unicode <pR
	latex +_{p\cal{R}}
symbol
	ascii .pR
	unicode ∙pP
	latex \cdot_{p\cal{R}}
symbol
	ascii -1R.
	unicode -1R
	latex -1_{\cal{R}}
symbol
	ascii .R
	unicode ∙R
	latex \cdot_{\cal{R}}
symbol
	ascii <R
	unicode <R
	latex <_{\cal{R}}
symbol
	ascii <RR
	unicode <ℝ
	latex <_{\mathbb{R}}
symbol
	ascii CC
	unicode ℂ
	latex \mathbb{C}
symbol
	ascii RR
	unicode ℝ
	latex \mathbb{R}
symbol
	ascii x.
	unicode ∙
	latex \cdot
symbol
	ascii +oo
	unicode +∞
	latex +\infty
symbol
	ascii -oo
	unicode -∞
	latex -\infty
symbol
	ascii RR*
	unicode ℝ*
	latex \mathbb{R}*
symbol
	ascii <_
	unicode ≤
	latex \le
symbol
	ascii NN
	unicode ℕ
	latex \mathbb{N}
symbol
	ascii NN0
	unicode ℕ₀
	latex \mathbb{N}_0
symbol
	ascii ZZ
	unicode ℤ
	latex \mathbb{Z}
symbol
	ascii QQ
	unicode ℚ
	latex \mathbb{Q}
symbol
	ascii RR+
	unicode ℝ⁺
	latex \mathbb{R}^+
symbol
	ascii sqr
	unicode √
	latex \surd
symbol
	ascii Re
	unicode ℜ
	latex \Re
symbol
	ascii Im
	unicode ℑ
	latex \Im
symbol
	ascii |_
	unicode ⌊
	latex \lfloor
symbol
	ascii ==
	unicode ≡
	latex \equiv
symbol
	ascii seq1
	unicode seq₁
	latex \rm{seq}_1
symbol
	ascii ZZ>=
	unicode ℤ≥
	latex \mathbb{Z}_\ge
symbol
	ascii seq0
	unicode seq₀
	latex \rm{seq}_0
symbol
	ascii ^
	unicode ↑
	latex \uparrow
symbol
	ascii ~~>
	unicode ⇝
	latex \rightsquigarrow
symbol
	ascii ...
	unicode ...
	latex \ldots
symbol
	ascii sum_
	unicode ∑
	latex \Sigma
symbol
	ascii _e
	unicode ℇ
	latex \rm{e}
symbol
	ascii pi
	unicode π
	latex \pi
symbol
	ascii -cn->
	unicode ‒cn→
	latex \longrightarrow_{\rm{cn}}
symbol
	ascii ~~>m
	unicode ⇝m
	latex \rightsquigarrow_{\rm{m}}
symbol
	ascii Id
	unicode _Id
	latex \rm{Id}
symbol
	ascii ^g
	unicode ↑g
	latex \uparrow_g
symbol
	ascii .s
	unicode ∙s
	latex \cdot_s
symbol
	ascii .i
	unicode ∙i
	latex \cdot_i
symbol
	ascii ~~>v
	unicode ⇝v
	latex \rightsquigarrow_{\rm{v}}
symbol
	ascii _|_
	unicode ⊥
	latex \perp
symbol
	ascii vH
	unicode ∨H
	latex \vee_\mathfrak{H}
symbol
	ascii \/H
	unicode VH
	latex \bigvee_\mathfrak{H}
symbol
	ascii <_op
	unicode ≤op
	latex \le_{\rm{op}}
symbol
	ascii Lambda
	unicode Λ
	latex \Lambda
symbol
	ascii <o
	unicode ⋖
	latex \lessdot
symbol
	ascii 1stc
	unicode 1stω
	latex 1^{\rm{st}}\omega
symbol
	ascii 2ndc
	unicode 2ndω
	latex 2^{\rm{nd}}\omega
symbol
	ascii prod_
	unicode ‏∏
	latex \Pi
symbol
	ascii (+)
	unicode ⊕
	latex \oplus
symbol
	ascii ~~>t
	unicode ⇝t
	latex \rightsquigarrow_{\rm{t}}
symbol
	ascii =~ph
	unicode =~φ
	latex \mbox{$=$\~{}ph}
symbol
	ascii ->..
	unicode ⇒
	latex \Longrightarrow
*/
}} // mdl::smm

