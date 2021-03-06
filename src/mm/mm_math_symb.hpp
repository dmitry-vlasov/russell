#pragma once

#include "mm_sys.hpp"

namespace mdl { namespace mm {

struct Constant {
	Constant(uint s, uint a, uint l) :
		symb(s), ascii(a), latex(l) { }
	const uint symb;
	const uint ascii;
	const uint latex;
};

struct Variable {
	Variable(uint v) : var(v) { }
	const uint var;
};

inline Constant make_const(const char* ascii, const char* unicode, const char* latex) {
	return Constant(Lex::toInt(unicode), Lex::toInt(ascii), Lex::toInt(latex));
}

inline uint make_key(const char* key) {
	return Lex::toInt(key);
}

inline map<uint, Constant>& math_consts() {
	static map<uint, Constant> table = {
		{make_key("|-"), make_const("|-", "⊢", "vdash")},
		{make_key("->"), make_const("->", "→", "\\rightarrow")},
		{make_key("-."), make_const("-.", "¬", "\\lnot")},
		{make_key("<->"), make_const("<->", "↔", "\\leftrightarrow")},
		{make_key("\\/"), make_const("\\/", "∨", "\\lor")},
		{make_key("/\\"), make_const("/\\", "∧", "\\land")},
		{make_key("-/\\"), make_const("-/\\", "⊼", "\\bar{\\wedge}")},
		{make_key("A."), make_const("A.", "∀", "\\forall")},
		{make_key("E."), make_const("E.", "∃", "\\exists")},
		{make_key("e."), make_const("e.", "∈", "\\in")},
		{make_key("E!"), make_const("E!", "∃!", "\\exists{!}")},
		{make_key("E*"), make_const("E*", "∃*", "\\exists^{\\ast}")},
		{make_key("{"), make_const("{", "{", "\\{")},
		{make_key("}"), make_const("}", "}", "\\}")},
		{make_key("=/="), make_const("=/=", "≠", "\\ne")},
		{make_key("e/"), make_const("e/", "∉", "\\notin")},
		{make_key("V"), make_const("V", "𝐕", "\\rm{V}")},
		{make_key("[_"), make_const("[_", "[_", "[")},
		{make_key("]_"), make_const("]_", "]_", "]")},
		{make_key("C_"), make_const("C_", "⊆", "\\subseteq")},
		{make_key("C."), make_const("C.", "⊂", "\\subset")},
		{make_key("\\"), make_const("\\", "∖", "\\setminus")},
		{make_key("u."), make_const("u.", "∪", "\\cup")},
		{make_key("i^i"), make_const("i^i", "∩", "\\cap")},
		{make_key("(/)"), make_const("(/)", "∅", "\\emptyset")},
		{make_key("~P"), make_const("~P", "Pow", "\\cal{P}")},
		{make_key("<."), make_const("<.", "〈", "\\langle")},
		{make_key(">."), make_const(">.", "〉", "\\rangle")},
		{make_key("U."), make_const("U.", "⋃", "\\bigcup")},
		{make_key("|^|"), make_const("|^|", "⋂", "\\bigcap")},
		{make_key("U_"), make_const("U_", "⋃_", "\\bigcup")},
		{make_key("|^|_"), make_const("|^|_", "⋂_", "\\bigcap")},
		{make_key("_E"), make_const("_E", "𝛜", "\\epsilon")},
		{make_key("_I"), make_const("_I", "_I", "\\rm{Id}")},
		{make_key("om"), make_const("om", "ω", "\\omega")},
		{make_key("X."), make_const("X.", "×", "\\times")},
		{make_key("`'"), make_const("`'", "⁻¹", "{}^{-1}")},
		{make_key("|`"), make_const("|`", "↾", "\\upharpoonright")},
		{make_key("\""), make_const("\"", "\"", "``")},
		{make_key("o."), make_const("o.", "∘", "\\circ")},
		{make_key("-->"), make_const("-->", "⟶", "\\longrightarrow")},
		{make_key("-1-1->"), make_const("-1-1->", "↣", "\\rightarrowtail")},
		{make_key("-onto->"), make_const("-onto->", "↠", "\\twoheadrightarrow")},
		{make_key("-1-1-onto->"), make_const("-1-1-onto->", "⤖", "\\rightarrowtail\\twoheadrightarrow")},
		{make_key("X_"), make_const("X_", "×_", "\\times")},
		{make_key("|->"), make_const("|->", "↦", "\\mapsto")},
		{make_key("^m"), make_const("^m", "↑m", "\\uparrow_m")},
		{make_key("^pm"), make_const("^pm", "↑pm", "\\uparrow_{pm}")},
		{make_key("+o"), make_const("+o", "+ₒ", "+_o")},
		{make_key(".o"), make_const(".o", "∙ₒ", "\\cdot_o")},
		{make_key("^o"), make_const("^o", "↑ₒ", "\\uparrow_o")},
		{make_key("1o"), make_const("1o", "1ₒ", "1_o")},
		{make_key("2o"), make_const("2o", "2ₒ", "2_o")},
		{make_key("/."), make_const("/.", "/.", "\\diagup")},
		{make_key("~~"), make_const("~~", "≈", "\\approx")},
		{make_key("~<_"), make_const("~<_", "≼", "\\preccurlyeq")},
		{make_key("~<"), make_const("~<", "≺", "\\prec")},
		{make_key("aleph"), make_const("aleph", "ℵ", "\\aleph")},
		{make_key("+c"), make_const("+c", "+𝐜", "+_c")},
		{make_key("R1"), make_const("R1", "R₁", "R_1")},
		{make_key(".N"), make_const(".N", "∙N", "\\cdot_{\\cal{N}}")},
		{make_key("<N"), make_const("<N", "<N", "<_{\\cal{N}}")},
		{make_key("+pQ"), make_const("+pQ", "+pQ", "+_{p\\cal{Q}}")},
		{make_key(".pQ"), make_const(".pQ", "∙pQ", "\\cdot_{p\\cal{Q}}")},
		{make_key("Q."), make_const("Q.", "Q.", "\\cal{Q}")},
		{make_key(".Q"), make_const(".Q", "∙Q", "\\cdot_{\\cal{Q}}")},
		{make_key("P."), make_const("P.", "Pos", "\\rm{Pos}")},
		{make_key("1P"), make_const("1P", "1Pos", "1_{\\rm{Pos}}")},
		{make_key("+P."), make_const("+P.", "+Pos", "+_{\\rm{Pos}}")},
		{make_key(".P."), make_const(".P.", "∙Pos", "\\cdot_{\\rm{Pos}}")},
		{make_key("<P"), make_const("<P", "<Pos", "<_{\\rm{Pos}}")},
		{make_key("+pR"), make_const("+pR", "+pR", "+_{p\\cal{R}}")},
		{make_key(".pR"), make_const(".pR", "∙pR", "\\cdot_{p\\cal{R}}")},
		{make_key("-1R"), make_const("-1R", "-1R", "-1_{p\\cal{R}}")},
		{make_key(".R"), make_const(".R", "∙R", "\\cdot_{p\\cal{R}}")},
		{make_key("<R"), make_const("<R", "<R", "<_{p\\cal{R}}")},
		{make_key("<RR"), make_const("<RR", "<ℝ", "<_{\\mathbb{R}}")},
		{make_key("CC"), make_const("CC", "ℂ", "\\mathbb{C}")},
		{make_key("RR"), make_const("RR", "ℝ", "\\mathbb{R}")},
		{make_key("x."), make_const("x.", "∙", "\\cdot")},
		{make_key("+oo"), make_const("+oo", "+∞", "+\\infty")},
		{make_key("-oo"), make_const("-oo", "-∞", "-\\infty")},
		{make_key("RR*"), make_const("RR*", "ℝ*", "\\mathbb{R}*")},
		{make_key("<_"), make_const("<_", "≤", "\\le")},
		{make_key("NN"), make_const("NN", "ℕ", "\\mathbb{N}")},
		{make_key("NN0"), make_const("NN0", "ℕ₀", "\\mathbb{N}_0")},
		{make_key("ZZ"), make_const("ZZ", "ℤ", "\\mathbb{Z}")},
		{make_key("QQ"), make_const("QQ", "ℚ", "\\mathbb{Q}")},
		{make_key("RR+"), make_const("RR+", "ℝ⁺", "\\mathbb{R}^+")},
		{make_key("sqr"), make_const("sqr", "√", "\\surd")},
		{make_key("Re"), make_const("Re", "ℜ", "\\Re")},
		{make_key("Im"), make_const("Im", "ℑ", "\\Im")},
		{make_key("|_"), make_const("|_", "⌊", "\\lfloor")},
		{make_key("=="), make_const("==", "≡", "\\equiv")},
		{make_key("seq1"), make_const("seq1", "seq₁", "\\rm{seq}_1")},
		{make_key("ZZ>="), make_const("ZZ>=", "ℤ≥", "\\mathbb{Z}_\\ge")},
		{make_key("seq0"), make_const("seq0", "seq₀", "\\rm{seq}_0")},
		{make_key("^"), make_const("^", "↑", "\\uparrow")},
		{make_key("~~>"), make_const("~~>", "⇝", "\\rightsquigarrow")},
		{make_key("..."), make_const("...", "...", "\\ldots")},
		{make_key("sum_"), make_const("sum_", "∑", "\\sigma")},
		{make_key("_e"), make_const("_e", "ℇ", "\\rm{e}")},
		{make_key("pi"), make_const("pi", "π", "\\pi")},
		{make_key("-cn->"), make_const("-cn->", "‒cn→", "\\longrightarrow_{\\rm{cn}}")},
		{make_key("~~>m"), make_const("~~>m", "⇝m", "\\rightsquigarrow_{\\rm{m}}")},
		{make_key("Id"), make_const("Id", "Id", "\\rm{Id}")},
		{make_key("^g"), make_const("^d", "↑g", "\\uparrow_g")},
		{make_key(".s"), make_const(".s", "∙s", "\\cdot_s")},
		{make_key(".i"), make_const(".i", "∙i", "\\cdot_i")},
		{make_key("~~>v"), make_const("~~>v", "⇝v", "\\rightsquigarrow_{\\rm{v}}")},
		{make_key("_|_"), make_const("_|_", "⊥", "\\perp")},
		{make_key("vH"), make_const("vH", "vH", "\\vee_\\mathfrak{H}")},
		{make_key("\\/H"), make_const("\\/H", "\\/H", "\\bigvee_\\mathfrak{H}")},
		{make_key("<_op"), make_const("<_op", "≤op", "\\le_{\\rm{op}}")},
		{make_key("Lambda"), make_const("Lambda", "Λ", "\\Lambda")},
		{make_key("<o"), make_const("<o", "⋖", "\\lessdot")},
		{make_key("1stc"), make_const("1stc", "1stω", "1^{\\rm{st}}\\omega")},
		{make_key("2ndc"), make_const("2ndc", "2ndω", "2^{\\rm{nd}}\\omega")},
		{make_key("prod_"), make_const("prod_", "∏", "\\Pi")},
		{make_key("(+)"), make_const("(+)", "⊕", "\\oplus")},
		{make_key("~~>t"), make_const("~~>t", "⇝t", "\\rightsquigarrow_{\\rm{t}}")},
		{make_key("=~ph"), make_const("=~ph", "=~φ", "\\mbox{$=$\\~{}ph}")},
		{make_key("->.."), make_const("->..", "⇒", "\\Longrightarrow")},
	};
	return table;
}
// Weird variables
inline map<uint, Variable>& math_vars() {
	static map<uint, Variable> table = {
			{make_key(".,"),   Variable(Lex::toInt("xcm"))},
			{make_key(".(x)"), Variable(Lex::toInt("xml"))},
			{make_key(".(+)"), Variable(Lex::toInt("xpl"))}
	};
	return table;
}


}}
