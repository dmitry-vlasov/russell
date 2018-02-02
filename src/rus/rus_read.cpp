#include <rus_sys.hpp>
#include <rus_ast.hpp>

namespace mdl { namespace rus {

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
		src->read();
		const string& data = src->data();
		new_sources.push_back(label);

		string imp;
		bool inside_imp = false;
		bool inside_ml_comm = false; // multi-line comment
		bool inside_sl_comm = false; // single-line comment

		for (auto i = data.begin(); i != data.end(); ++ i) {
			if (inside_imp) imp += *i;
			switch (*i) {
			case 'i' : {
				++i;
				if (inside_imp) imp += *i;
				if (!(inside_sl_comm || inside_ml_comm || inside_imp)) {
					if (*i == 'm') {
						++i;
						if (*i == 'p') {
							++i;
							if (*i == 'o') {
								++i;
								if (*i == 'r') {
									++i;
									if (*i == 't') {
										inside_imp = true;
									}
								}
							}
						}
					}
				}
				break;
			}
			case '/' : {
				++i;
				if (inside_imp) imp += *i;
				switch (*i) {
				case '/': inside_sl_comm = true; break;
				case '*': inside_ml_comm = true; break;
				}
				break;
			}
			case '*' : {
				++i;
				if (inside_imp) imp += *i;
				if (*i == '/') {
					if (inside_imp) imp += *i;
					inside_ml_comm = false;
				}
				break;
			}
			case '\n': {
				inside_sl_comm = false;
				break;
			}
			case ';' : {
				++i;
				if (*i == ';') {
					if (inside_imp && !(inside_sl_comm || inside_ml_comm)) {
						inside_imp = false;
						boost::trim(imp);
						uint imp_label = Lex::toInt(Path::trim_ext(imp));
						imp.clear();
						includes[label].insert(imp_label);
						to_read.push(imp_label);
					}
				}
				break;
			}
			default: break;
			}
		}
	}
	for (auto s : new_sources) {
		for (auto inc : includes[s]) {
			auto inc_src = Sys::mod().math.get<Source>().access(inc);
			Sys::mod().math.get<Source>().access(s)->include(inc_src);
		}
	}
	for (auto s : new_sources) {
		Source* src = Sys::mod().math.get<Source>().access(s);
		src->transitive_closure();
	}
}

}}
