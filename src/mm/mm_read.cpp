#include <mm_sys.hpp>
#include <mm_ast.hpp>

namespace mdl { namespace mm {

static vector<Patch> const_patches = {
{
R"(
  $c har ~<_* $.
)",
R"(
  $c har $.
  $c ~<_* $.
)"
},
{
R"(
  $c Fin1a Fin2 Fin3 Fin4 Fin5 Fin6 Fin7 $.
)",
R"(
  $c Fin1a $.
  $c Fin2 $.
  $c Fin3 $.
  $c Fin4 $.
  $c Fin5 $.
  $c Fin6 $.
  $c Fin7 $.
)"
},
{
R"(
  $c numer denom $.
)",
R"(
  $c numer $.
  $c denom $.
)"
},
{
R"(
  $c Xs_ ^s $.
)",
R"(
  $c Xs_ $.
  $c ^s $.
)"
},
{
R"(
  $c Moore mrCls mrInd ACS $.
)",
R"(
  $c Moore $.
  $c mrCls $.
  $c mrInd $.
  $c ACS $.
)"
},
{
R"(
  $c Preset Dirset $.
)",
R"(
  $c Preset $.
  $c Dirset $.
)"
},
{
R"(
  $c <" "> $.
)",
R"(
  $c <" $.
  $c "> $.
)"
},
{
R"(
  $c No <s bday $.
)",
R"(
  $c No $.
  $c <s $.
  $c bday $.
)"
},
{
R"(
  $c (x) Bigcup SSet Trans Limits Fix Funs Singleton Singletons Image Cart $.
  $c Img Domain Range pprod Apply Cup Cap Succ Funpart FullFun Restrict $.
)",
R"(
  $c (x) $.
  $c Bigcup $.
  $c SSet $.
  $c Trans $.
  $c Limits $.
  $c Fix $.
  $c Funs $.
  $c Singleton $.
  $c Singletons $.
  $c Image $.
  $c Cart $.

  $c Img $.
  $c Domain $.
  $c Range $.
  $c pprod $.
  $c Apply $.
  $c Cup $.
  $c Cap $.
  $c Succ $.
  $c Funpart $.
  $c FullFun $.
  $c Restrict $.
)"
},
{
R"(
  $c << >> XX. $.
)",
R"(
  $c << $.
  $c >> $.
  $c XX. $.
)"
},
{
R"(
  $c EE Btwn Cgr $.
)",
R"(
  $c EE $.
  $c Btwn $.
  $c Cgr $.
)"
},
{
R"(
  $c InnerFiveSeg Cgr3 Colinear FiveSeg $.
)",
R"(
  $c InnerFiveSeg $.
  $c Cgr3 $.
  $c Colinear $.
  $c FiveSeg $.
)"
},
{
R"(
  $c Line LinesEE Ray $.
)",
R"(
  $c Line $.
  $c LinesEE $.
  $c Ray $.
)"
},
{
R"(
  $c Pell1QR Pell14QR Pell1234QR PellFund []NN $.
)",
R"(
  $c Pell1QR $.
  $c Pell14QR $.
  $c Pell1234QR $.
  $c PellFund $.
  $c []NN $.
)"
},
{
R"(
  $c rmX rmY $.
)",
R"(
  $c rmX $.
  $c rmY $.
)"
},
{
R"(
  $c freeLMod unitVec $.
)",
R"(
  $c freeLMod $.
  $c unitVec $.
)"
},
{
R"(
  $c LIndF LIndS $.
)",
R"(
  $c LIndF $.
  $c LIndS $.
)"
},
{
R"(
  $c Monic Poly< $.
)",
R"(
  $c Monic $.
  $c Poly< $.
)"
},
{
R"(
  $c degAA minPolyAA $.
)",
R"(
  $c degAA $.
  $c minPolyAA $.
)"
},
{
R"(
  $c _ZZ IntgOver $.
)",
R"(
  $c _ZZ $.
  $c IntgOver $.
)"
},
{
R"(
  $c maMul Mat $.
)",
R"(
  $c maMul $.
  $c Mat $.
)"
},
{
R"(
  $c maDet maAdju $.
)",
R"(
  $c maDet $.
  $c maAdju $.
)"
},
{
R"(
  $c TopSep TopLnd $.
)",
R"(
  $c TopSep $.
  $c TopLnd $.
)"
},
{
R"(
  $c +r -r .v PtDf RR3 plane3 line3 $.
)",
R"(
  $c +r $.
  $c -r $.
  $c .v $.
  $c PtDf $.
  $c RR3 $.
  $c plane3 $.
  $c line3 $.
)"
},
{
R"(
  $c LPIdeal LPIR $.
)",
R"(
  $c LPIdeal $.
  $c LPIR $.
)"
},
{
R"(
  $c hadd cadd $.
)",
R"(
  $c hadd $.
  $c cadd $.
)"
},
{
R"(
  $c +r -r .v PtDf RR3 $( plane3 $) line3 $.
)",
R"(
  $c +r $.
  $c -r $.
  $c .v $.
  $c PtDf $.
  $c RR3 $.
  $c line3 $. $( plane3 $)
)"
}
};

void read(uint label) {
	delete Sys::get().math.get<Source>().access(label);
	queue<uint> to_read;
	to_read.push(label);

	map<uint, set<uint>> includes;
	vector<uint> new_sources;

	while (!to_read.empty()) {
		label = to_read.front(); to_read.pop();
		if (Sys::get().math.get<Source>().has(label)) continue;

		Source* src = new Source(label);
		src->read(&const_patches);
		const string& data = src->data();
		new_sources.push_back(label);

		string inc;
		bool inside_inc = false;
		bool inside_comm = false;

		for (auto i = data.begin(); i != data.end(); ++ i) {
			if (*i == '$') {
				++i;
				if (*i == '[' && !inside_comm) {
					++i;
					inside_inc = true;
				}
				if (*i == ']' && !inside_comm) {
					++i;
					inside_inc = false;
					boost::trim(inc);
					uint inc_label = Lex::toInt(Path::trim_ext(inc));
					inc.clear();
					includes[label].insert(inc_label);
					to_read.push(inc_label);
				}
				if (*i == '(') { ++i; inside_comm = true; }
				if (*i == ')') { ++i; inside_comm = false; }
			} else {
				if (inside_inc) inc += *i;
			}
		}
	}
	for (auto s : new_sources) {
		for (auto inc : includes[s]) {
			auto inc_src = Sys::mod().math.get<Source>().access(inc);
			Sys::mod().math.get<Source>().access(s)->include(inc_src);
		}
	}
}

}}
