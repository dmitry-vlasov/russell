#pragma once

#include "rus_ast.hpp"

namespace mdl { namespace rus { namespace prover {

struct LightSymbol {
	LightSymbol() : lit(-1), rep(false), type(nullptr) { }
	LightSymbol(uint l, const Type* t, bool r = true) : lit(l), rep(r), type(t) { }
	LightSymbol(const LightSymbol& s) = default;

	bool is_undef() const { return lit == -1; }
	bool is_def() const { return lit != -1; }

	bool operator == (const LightSymbol& s) const { return lit == s.lit; }
	bool operator != (const LightSymbol& s) const { return !operator ==(s); }
	bool operator == (uint s) const { return lit == s; }
	bool operator != (uint s) const { return !operator ==(s); }
	bool operator < (const LightSymbol& s) const { return lit < s.lit; }

	LightSymbol& operator = (const LightSymbol& s) = default;
	LightSymbol& operator = (const Symbol& s) {
		lit = s.lit();
		type = s.type();
		rep = (s.kind() == Symbol::VAR);
		return *this;
	}

	string show() const {
		return is_undef() ? "<UNDEF>" : Lex::toStr(lit);
	}

	struct Hash {
		typedef size_t result_type;
		typedef Symbol argument_type;
		size_t operator() (const LightSymbol& s) const {
			return hash(s.lit);
		}
	private:
		static std::hash<uint> hash;
	};

	uint lit;
	bool rep;
	const Type* type;
};

string show(const set<uint>&);
string show(const vector<uint>&);
string show(const vector<bool>& v);
string show(const vector<LightSymbol>& v);

inline ostream& operator << (ostream& os, const LightSymbol& s) {
	os << s.show(); return os;
}

struct VarProvider {
	static LightSymbol makeVarZero(uint lit, const Type* type) {
		return LightSymbol(addIndex(lit, 0), type, true);
	}
	static LightSymbol makeVar(uint lit, const Type* type) {
		return LightSymbol(lit, type, true);
	}
	LightSymbol makeFreshVar(uint lit, const Type* type) {
		auto it = vars.find(lit);
		// 0 index is reserved for assertion vars
		uint fresh_ind = it != vars.end() ? it->second + 1 : 1;
		uint fresh_lit = addIndex(lit, fresh_ind);
		vars[lit] = fresh_ind;
		return LightSymbol(fresh_lit, type, true);
	}
	string show() const {
		ostringstream oss;
		for (auto& p : vars) {
			oss << Lex::toStr(p.first) << " -> " << p.second << endl;
		}
		return oss.str();
	}
private:
	static uint addIndex(uint lit, uint ind) {
		return (ind == -1) ? lit : Lex::toInt(Lex::toStr(lit) + "_" + to_string(ind));
	}
	map<uint, uint> vars;
};

}}}
