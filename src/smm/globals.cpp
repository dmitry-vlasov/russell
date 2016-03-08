/*****************************************************************************/
/* Project name:    smm - verifier for the Simplified MetaMath language      */
/* File Name:       smm_main.cpp                                             */
/* Description:     main function for smm                                    */
/* Copyright:       (c) 2006-2010 Dmitri Vlasov                              */
/* Author:          Dmitri Yurievich Vlasov, Novosibirsk, Russia             */
/* Email:           vlasov at academ.org                                     */
/* URL:             http://mathdevlanguage.sourceforge.net                   */
/* Modified by:                                                              */
/* License:         GNU General Public License Version 3                     */
/*****************************************************************************/

#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

	void Smm::run()
	{
		timers.total.start();
		if (config.verbose)
			cout << "verifying file " << config.in << " ... " << flush;
		if (!parse()) {
			failed = true; return;
		}
		if (!verify()) {
			failed = true; return;
		}
		timers.total.stop();
		if (config.verbose)
			cout << "done in " << timers.total << endl;
	}
	bool Smm::parse()
	{
		try {
			timers.read.start();
			source = parse1::source(config.in);

			//cout << *source << endl;

			timers.read.stop();
			return true;
		} catch (Error& err) {
			status += '\n';
			status += err.what();
			failed = true;
			return false;
		}
	}
	bool Smm::verify()
	{
		try {
			timers.verify.start();
			verify::math(math.assertions);
			timers.verify.stop();
			return true;
		} catch (Error& err) {
			status += '\n';
			status += err.what();
			failed = true;
			return false;
		}
	}
	void Smm::show (string& str) const {
		str += status;
	}
	
}} // mdl::smm
