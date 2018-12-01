/*
    Copyright (c) 2016 Juraj Major

    This file is part of LTL3TELA.

    LTL3TELA is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    LTL3TELA is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with LTL3TELA.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <iostream>
#include <fstream> //
#include <spot/misc/version.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/tl/unabbrev.hh>
#include <spot/tl/nenoform.hh>
#include <spot/tl/simplify.hh>
#include <spot/twaalgos/dot.hh>
#include <spot/twaalgos/dualize.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twa/twagraph.hh>
#include <string>
#include "utils.hpp"
#include "alternating.hpp"
#include "semideterministic.hpp"
#include "automaton.hpp"

bool o_single_init_state;	// -i
bool o_vwaa_determ;			// -d
unsigned o_eq_level;		// -e
unsigned o_debug_mode;		// -g
bool o_mergeable_info;		// -m
bool o_ac_filter_fin;		// -t
bool o_spot_simulation;		// -u
bool o_spot_scc_filter;		// -z

bool o_x_single_succ;		// -X

int main(int argc, char* argv[])
{
	std::string version("1.1.1");

	bdd_init(1000, 1000);
	// hide "garbage collection" messages from BuDDy
	bdd_gbc_hook(nullptr);

	std::map<std::string, std::string> args = parse_arguments(argc, argv);

	if (args.count("v") > 0) {
		std::cout << "LTL2sDBA " << version << " (using Spot " << spot::version() << ")\n";
		return 0;
	}

	bool invalid_run = args.count("f") == 0;

	if (invalid_run || args.count("h") > 0) {
		std::cout << "LTL2sDBA " << version << " (using Spot " << spot::version() << ")\n\n"
			<< "usage: " << argv[0] << " [-flags] -f formula\n"
			<< "available flags:\n"
			<< "\t-a[0|2|3]\tact like\n"
			<< "\t\t0\tdo not simulate anything (default)\n"
			<< "\t\t2\tltl2ba (like -d0 -u0 -n0 -e1)\n"
			<< "\t\t3\tltl3ba (like -u0 -n0 -i1 -X1)\n"
			<< "\t-d[0|1]\tmore deterministic VWAA construction (default on)\n"
			<< "\t-e[0|1|2]\tequivalence check on NA\n"
			<< "\t\t0\tno check\n"
			<< "\t\t1\tltl2ba's simple check\n"
			<< "\t\t2\tltl3ba's improved check (default)\n"
			<< "\t-g[0|1]\tprint debug messages (default off)\n"
			<< "\t-h, -?\tprint this help\n"
			<< "\t-i[0|1]\tproduce VWAA with one initial state (default off for printing phase 1, otherwise fixed as on)\n"
			<< "\t-m[0|1]\tcheck formula for containment of some alpha-mergeable U (default off)\n"
			<< "\t-n[0|1]\ttry translating !f and complementing the automaton (default on) -currently disabled function\n"
			<< "\t-o [hoa|dot]\ttype of output\n"
			<< "\t\thoa\tprint automaton in HOA format (default)\n"
			<< "\t\tdot\tprint dot format\n"
			<< "\t-p[1|2|3]\tphase of translation (default 2)\n"
			<< "\t\t1\tprint VWAA\n"
			<< "\t\t2\tprint NA with removed alternation\n"
			<< "\t\t3\tprint both\n"
			<< "\t-s[0|1]\tspot's formula simplifications (default on)\n"
			<< "\t-t[0|1]\timproved construction of acceptance condition (default on)\n"
			<< "\t-u[0|1]\tsimulation of nondeterministic automaton (default on)\n"
			<< "\t-v\tprint version and exit\n"
			<< "\t-X[0|1]\ttranslate X phi as (X phi) --tt--> (phi) (default off)\n"
			<< "\t-z[0|1]\tcall scc_filter on nondeterministic automaton (default on)\n";

		return invalid_run;
	}

	spot::formula f;
	try {
		f = spot::parse_formula(args["f"]);
	} catch (spot::parse_error& e) {
		std::cerr << "The input formula is invalid.\n" << e.what();
		return 1;
	}

	o_vwaa_determ = std::stoi(args["d"]);
	o_eq_level = std::stoi(args["e"]);
	o_debug_mode = std::stoi(args["g"]);
	o_mergeable_info = std::stoi(args["m"]);
	o_ac_filter_fin = std::stoi(args["t"]);
	o_spot_simulation = std::stoi(args["u"]);
	o_spot_scc_filter = std::stoi(args["z"]);


	o_x_single_succ = std::stoi(args["X"]);

	unsigned int print_phase = std::stoi(args["p"]);
	unsigned int try_negation = std::stoi(args["n"]);

    if (print_phase & 1) {
        o_single_init_state = std::stoi(args["i"]);
    } else {
        o_single_init_state = 1;
    }

	spot::twa_graph_ptr sdba = nullptr;

	try {
			f = spot::negative_normal_form(spot::unabbreviate(f));

			if (args["s"] == "1") {
				spot::tl_simplifier tl_simplif;
				f = tl_simplif.simplify(f);
			}

			f = spot::unabbreviate(f);

			auto vwaa = make_alternating(f);

			if (o_mergeable_info) {
				// If some mergeable is present, true is already output
				// from the call of is_mergeable
				std::cout << false << std::endl;
				std::exit(0);
			}

			if (o_spot_scc_filter || print_phase == 2) {
				vwaa->remove_unreachable_states();
				vwaa->remove_unnecessary_marks();
			}

			if (print_phase & 1) { // If print_phase is 1 or 3
				if (args["o"] == "dot") {
					vwaa->print_dot();
				} else {
					vwaa->print_hoaf();
				}
			}

			if (print_phase & 2) { // If print_phase is 2 or 3

				if (!o_spot_scc_filter && print_phase != 2) {
					vwaa->remove_unreachable_states();
					vwaa->remove_unnecessary_marks();
				}

				auto sdba_temp = make_semideterministic(vwaa, o_debug_mode);
				sdba = sdba_temp;

			}
            delete vwaa;

	} catch (std::runtime_error& e) {
		std::string what(e.what());

		// This should not happen since we are not working with acceptance marks, but it is left in just in case
		if (what == "Too many acceptance sets used.") {
			std::cerr << "LTL2SDBA is unable to set more than 32 acceptance marks.\n";
			return 32;
		}
	}

	// Removing alternation and printing SDBA
	if (print_phase & 2) {

		if (args["o"] == "dot") {
			spot::print_dot(std::cout, sdba);
		} else {
		    spot::print_hoa(std::cout, sdba);
			std::cout << '\n';
		}
	}

	// We do not call bdd_done(), as we use libbddx
	return 0;
}
