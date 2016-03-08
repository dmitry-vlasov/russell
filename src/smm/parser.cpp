#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

class Token {
public :
	enum Type {
		UNKNOWN,    ///< unknown token
		CONSTANT,   ///< "$c"
		VARIABLE,   ///< "$v"
		FLOATING,   ///< "$f"
		DISJOINTED, ///< "$d"
		ESSENTIAL,  ///< "$e"
		AXIOMATIC,  ///< "$a"
		PROVABLE,   ///< "$p"
		EQUALITY,   ///< "$="
		END,        ///< "$."

		BLOCK_BEGIN,     ///< "${"
		BLOCK_END,       ///< "$}"
		INCLUSION_BEGIN, ///< "$["
		INCLUSION_END,   ///< "$]"

		LITERAL,  ///< string of any of 94 printable ASCI characters except for the '$' symbol.
		INDEX,    ///< assertion index - and non negative integer.
		LABEL,    ///< assertion label
		PATH,     ///< file path

		PREFIX_E, ///< "e"
		PREFIX_F, ///< "f"
		PREFIX_I, ///< "i"
		PREFIX_A, ///< "a"
		PREFIX_P, ///< "p"
		EOF_
	};

	Token(): type (UNKNOWN), body() {}
	Token(Type tp): type(tp), body () { }
	Token(Type tp, const string& str) : type (tp), body (str) { }

	Type   type;
	string body;
};

struct Reader {
	Reader(const string& file) :
	loc(file), ifs(nullptr), prevLoc(file), nextLoc(file) {
		ifs = new ifstream(file);
	}
	~Reader() {
		delete ifs;
	}

	bool get(char& ch) {
		bool ret = ifs->get(ch);
		prevLoc = loc;
		loc = nextLoc;
		if (ch == '\n') {
			nextLoc.col = 0;
			++ nextLoc.line;
		} else {
			++ nextLoc.col;
		}
		return ret;
	}
	char peek() const {
		return ifs->peek();
	}
	void unget() {
		loc = prevLoc;
		ifs->unget();
	}

	Location loc;

private:
	ifstream* ifs;
	Location  prevLoc;
	Location  nextLoc;
};

namespace lexer {

struct Context {
	Context() :
	inLiteral(false), inProof(false), inInclude(false),
	inLabel(false), inIndex(false) { }

	bool inLiteral;
	bool inProof;
	bool inInclude;
	bool inLabel;
	bool inIndex;
};

	void comment(Reader& rd) {
		char ch = '\0';
		while (rd.get(ch)) {
			if (ch == '$') {
				rd.get(ch);
				if (ch == ')') {
					break;
				}
			}
		}
	}
	void whitespace(Reader& rd) {
		char ch = '\0';
		while (rd.get(ch)) {
			if (isspace(ch)) {
				continue;
			}
			if (ch == '$') {
				if (rd.peek() == '(') {
					comment(rd);
					continue;
				} else {
					rd.unget();
					break;
				}
			} else {
				rd.unget();
				break;
			}
		}
	}

	template<int context>
	bool admit(char ch);

	template<>
	bool admit<Token::LITERAL>(char ch) {
		return !(isspace(ch) || ch == '$');
	}
	template<>
	bool admit<Token::LABEL>(char ch) {
		return (isalnum(ch) || ch == '_' || ch == '-' || ch == '.') && ch != '$';
	}
	template<>
	bool admit<Token::INDEX>(char ch) {
		return isdigit(ch) && ch != '$';
	}
	template<>
	bool admit<Token::PATH>(char ch) {
		return (isalnum(ch) || ch == '.' || ch == '_' || ch == '\\' || ch == '/') && ch != '$';
	}

	template<Token::Type context>
	Token consume_str(Reader& rd) {
		string body;
		char ch = '\0';
		while (rd.get (ch)) {
			if (admit<context>(ch)) {
				body += ch;
			} else {
				rd.unget();
				break;
			}
		}
		return Token (context, body);
	}

	Token consume_keyword(Reader& stream, Context& ctx) {
		char ch = '\0';
		if (!stream.get (ch)) return Token(Token::EOF_);
		if (ch != '$')  return Token();
		if (!stream.get (ch)) return Token(Token::EOF_);
		switch (ch) {
		case 'c' : ctx.inLiteral = true; return Token (Token::CONSTANT, "$c");
		case 'v' : ctx.inLiteral = true; return Token (Token::VARIABLE, "$v");
		case 'f' : ctx.inLiteral = true; return Token (Token::FLOATING, "$f");
		case 'd' : ctx.inLiteral = true; return Token (Token::DISJOINTED, "$d");
		case 'e' : ctx.inLiteral = true; return Token (Token::ESSENTIAL, "$e");
		case 'a' : ctx.inLiteral = true; return Token (Token::AXIOMATIC, "$a");
		case 'p' : ctx.inLiteral = true; return Token (Token::PROVABLE, "$p");
		case '=' :
			ctx.inLiteral = false;
			ctx.inProof = true;
			return Token (Token::EQUALITY, "$=");
		case '.' :
			ctx.inLiteral = false;
			ctx.inProof = false;
			return Token (Token::END);
		case '{' : return Token (Token::BLOCK_BEGIN, "${");
		case '}' : return Token (Token::BLOCK_END, "$}");
		case '[' : ctx.inInclude = true; return Token (Token::INCLUSION_BEGIN, "$[");
		case ']' : ctx.inInclude = false; return Token (Token::INCLUSION_END, "$]");
		default  : return Token();
		}
	}

	Token consume_prefix(Reader& rd, Context& ctx) {
		char ch = '\0';
		if (!rd.get (ch)) return Token(Token::EOF_);
		if (!Smm::get().config.labels) {
			ctx.inIndex = true;
		} else {
			switch (ch) {
				case 'f' :
				case 'e' :
				case 'i' :
					ctx.inIndex = true; break;
				case 'a' :
				case 'p' :
					ctx.inLabel = true; break;
				default : break;
			}
		}
		switch (ch) {
		case 'e' : return Token (Token::PREFIX_E, "e");
		case 'f' : return Token (Token::PREFIX_F, "f");
		case 'i' : return Token (Token::PREFIX_I, "i");
		case 'a' : return Token (Token::PREFIX_A, "a");
		case 'p' : return Token (Token::PREFIX_P, "p");
		default  : return Token();
		}
	}

	Token scan(Reader& rd) {
		whitespace (rd);
		static Context ctx;
		if (rd.peek() != '$') {
			if (ctx.inLiteral) {
				return consume_str<Token::LITERAL>(rd);
			} else if (ctx.inInclude) {
				return consume_str<Token::PATH>(rd);
			} else if (ctx.inLabel){
				ctx.inLabel = false;
				return consume_str<Token::LABEL>(rd);
			} else if (ctx.inIndex){
				ctx.inIndex = false;
				return consume_str<Token::INDEX>(rd);
			} else {
				return consume_prefix(rd, ctx);
			}
		} else {
			return consume_keyword(rd, ctx);
		}
	}
} // smm::lexer

namespace parse {

inline void token(Reader& rd, Token& tok, Token::Type tp) {
	tok = lexer::scan(rd);
	if (tok.type != tp) {
		throw Error("unexpected", tok.body, &rd.loc);
	}
}

static Expr expression(Reader& rd, Token& tok, bool vars = false, Token::Type end = Token::END) {
	Expr expr;
	for (tok = lexer::scan(rd); tok.type == Token::LITERAL; tok = lexer::scan(rd)) {
		Symbol symb(Smm::mod().lex.symbols.toInt(tok.body), vars);
		expr.symbols.push_back(symb);
	}
	if (tok.type != end) {
		throw Error("expected", "$.", &rd.loc);
	}
	return expr;
}

static Constants* consts(Reader& rd, Token& tok) {
	Constants* consts = new Constants();
	consts->expr = expression(rd, tok);
	return consts;
}

static Proof* proof(Reader& rd, Token& tok) {
	Proof* pr = new Proof();
	const Config& conf = Smm::get().config;
	for (tok = lexer::scan(rd); tok.type != Token::END; tok = lexer::scan(rd)) {
		Ref ref;
		switch (tok.type) {
		case Token::PREFIX_A: ref.type = Ref::PREF_A; break;
		case Token::PREFIX_P: ref.type = Ref::PREF_P; break;
		case Token::PREFIX_E: ref.type = Ref::PREF_E; break;
		case Token::PREFIX_F: ref.type = Ref::PREF_F; break;
		case Token::PREFIX_I: ref.type = Ref::PREF_I; break;
		default: throw Error("expected", "a, p, e, f, i", &rd.loc);
		}
		if (conf.labels &&
			(ref.type == Ref::PREF_A || ref.type == Ref::PREF_P)) {
			token(rd, tok, Token::LABEL);
			ref.index = Smm::mod().lex.labels.getInt(tok.body);
		} else {
			token(rd, tok, Token::INDEX);
			ref.index = std::stoi(tok.body);
		}
		pr->refs.push_back(ref);
	}
	return pr;
}


static void markVars(const vector<Variables>& vars, Expr& expr) {
	for (auto v_it = vars.cbegin(); v_it != vars.cend(); ++ v_it) {
		expr.markVars(v_it->expr);
	}
}

template<class T>
static void markVars(const vector<Variables>& vars, vector<T>& components) {
	for (auto ex_it = components.begin(); ex_it != components.end(); ++ ex_it) {
		markVars(vars, ex_it->expr);
	}
}

static Assertion* assertion(Reader& rd, Token& tok) {
	Assertion* ass = new Assertion(rd.loc);
	while (tok.type != Token::EOF_) {
		tok = lexer::scan(rd);
		Expr expr;
		switch (tok.type) {
		case Token::VARIABLE: {
			Variables vars;
			vars.expr = expression(rd, tok, true);
			ass->variables.push_back(vars);
		}	break;
		case Token::DISJOINTED: {
			Disjointed disj;
			disj.expr = expression(rd, tok, true);
			ass->disjointed.push_back(disj);
		}	break;
		case Token::PREFIX_E: {
			token(rd, tok, Token::INDEX);
			Essential ess;
			ess.index = std::stoi(tok.body);
			if (ass->essential.size() != ess.index)
				throw Error("Wrong essential index", tok.body, &rd.loc);
			token(rd, tok, Token::ESSENTIAL);
			ess.expr = expression(rd, tok);
			ass->essential.push_back(ess);
		}	break;
		case Token::PREFIX_I: {
			token(rd, tok, Token::INDEX);
			Inner inn;
			inn.index = std::stoi(tok.body);
			if (ass->inner.size() != inn.index)
				throw Error("Wrong inner index", tok.body, &rd.loc);
			token(rd, tok, Token::FLOATING);
			inn.expr = expression(rd, tok);
			ass->inner.push_back(inn);
		}	break;
		case Token::PREFIX_F: {
			token(rd, tok, Token::INDEX);
			Floating flo;
			flo.index = std::stoi(tok.body);
			if (ass->floating.size() != flo.index)
				throw Error("Wrong floating index", tok.body, &rd.loc);
			token(rd, tok, Token::FLOATING);
			flo.expr = expression(rd, tok);
			ass->floating.push_back(flo);
		}	break;
		case Token::PREFIX_A:
			ass->prop.axiom = true;
			if (Smm::get().config.labels) {
				token(rd, tok, Token::LABEL);
				ass->prop.label = Smm::mod().lex.labels.toInt(tok.body);
			} else {
				token(rd, tok, Token::INDEX);
				ass->prop.label = std::stoi(tok.body);
			}
			token(rd, tok, Token::AXIOMATIC);
			ass->prop.expr = expression(rd, tok);
			ass->proof = nullptr;
			goto out;
		case Token::PREFIX_P:
			ass->prop.axiom = false;
			if (Smm::get().config.labels)  {
				token(rd, tok, Token::LABEL);
				ass->prop.label = Smm::mod().lex.labels.toInt(tok.body);
			} else {
				token(rd, tok, Token::INDEX);
				ass->prop.label = std::stoi(tok.body);
			}
			token(rd, tok, Token::PROVABLE);
			ass->prop.expr = expression(rd, tok, false, Token::EQUALITY);
			ass->proof = proof(rd, tok);
			ass->proof->theorem = ass;
			goto out;
		default : throw Error("uexpected", tok.body, &rd.loc);
		}
	}
	out :
	token(rd, tok, Token::BLOCK_END);
	markVars(ass->variables, ass->floating);
	markVars(ass->variables, ass->essential);
	markVars(ass->variables, ass->prop.expr);
	return ass;
}

Source* source(const string& in, const string& root)
{
	stack<Reader*> readers;
	Source* source = new Source(in);
	readers.push(new Reader(in));
	Reader* rd = readers.top();
	while (true) {
		Token tok = lexer::scan(*rd);
		switch (tok.type) {
		case Token::CONSTANT:
			source->contents.push_back(consts(*rd, tok)); break;
		case Token::BLOCK_BEGIN: {
			Assertion* ass = assertion(*rd, tok);
			source->contents.push_back(ass);
			Smm::mod().math.assertions.push_back(ass);
		} break;
		case Token::INCLUSION_BEGIN: {
			string include = Smm::get().config.root;
			token(*rd, tok, Token::PATH);
			include += tok.body;
			readers.push(new Reader(include));
			rd = readers.top();
		}	break;
		case Token::EOF_:
			delete readers.top();
			readers.pop();
			if (readers.empty()) {
				goto end;
			}
			rd = readers.top();
			token(*rd, tok, Token::INCLUSION_END);
			break;
		default: throw Error("unexpected", tok.body, &rd->loc);
		}
	}
	end :
	return source;
}

}}} // mdl::smm::parser
