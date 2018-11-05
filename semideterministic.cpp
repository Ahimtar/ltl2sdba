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

#include "semideterministic.hpp"

// Converts a given VWAA to sDBA;
spot::twa_graph_ptr make_semideterministic(VWAA *vwaa, std::string debug) {

    // We first transform the VWAA into spot format

    // Creating helper files and saving current stream buffer
    std::ofstream outs;
    std::streambuf *coutbuf = std::cout.rdbuf();

    // Redirecting output into helper file and printing vwaa in hoa
    outs.open ("helper.hoa", std::ofstream::trunc);
    std::cout.rdbuf(outs.rdbuf());
    vwaa->print_hoaf();
    std::cout.rdbuf(coutbuf);
    outs.close();

    // Parsing the helper, acquiring spot format
    spot::parsed_aut_ptr pvwaaptr = parse_aut("helper.hoa", spot::make_bdd_dict());
    if (pvwaaptr->format_errors(std::cerr))
        return vwaa->spot_aut;  // todo returning random error, the file from printfile didnt create successfully
    if (pvwaaptr->aborted)
    {
        std::cerr << "--ABORT-- read\n";
        return vwaa->spot_aut;  // todo returning random error, the file from printfile didnt create successfully
    }
    auto pvwaa = pvwaaptr->aut;

    //_________________________________________________________________________________
    // We have VWAA parsed. Now, we assign Qmays and Qmusts and remove acceptance marks

    int nq = pvwaa->num_states();

    const spot::bdd_dict_ptr& dict = pvwaa->get_dict();

    bool isqmay[nq];
    bool isqmust[nq];

    auto snvwaa = pvwaa->get_named_prop<std::vector<std::string>>("state-names");

    // We iterate over all states of the VWAA
    for (unsigned q = 0; q < nq; ++q)
    {
        // Renaming state to its number instead of the LTL formula for later use
        (*snvwaa)[q] = std::to_string(q);

        isqmay[q] = false;
        // If there exists a looping, but not accepting outgoing edge, we set this state as Qmay
        for (auto& t: pvwaa->out(q))
        {
            for (unsigned d: pvwaa->univ_dests(t.dst))
            {
                if (t.src == d && t.acc.id == 0) {
                    isqmay[q] = true; // todo p4, confirms same state twice, fix?
                    if (debug == "1"){std::cout << q << " is Qmay. ";}
                    break;
                }
            }
        }

        isqmust[q] = true;
        bool thereIsALoop;
        // If we find an outgoing edge, where there is no loop, we set this state as not Qmust and break the loop
        for (auto& t: pvwaa->out(q))
        {
            thereIsALoop = false;
            for (unsigned d: pvwaa->univ_dests(t.dst))
            {
                if (t.src == d){
                    thereIsALoop = true;
                }
            }
            if (!thereIsALoop){
                isqmust[q] = false;
                if (debug == "1"){std::cout << q << " is not Qmust. ";}
                break;
            }
        }

        // todo save these acceptance marks for the r-component building
        // We remove acceptance marks from all the edges, since no edge in the nondeterministic part is accepting
        for (auto& t: pvwaa->out(q))
        {
            t.acc = 0;
        }
    }


    //_________________________________________________________________________________
    // We are done with the VWAA and can move on
    // We now start building the SDBA by removing alternation, which gives us the final nondeterministic part

    spot::twa_graph_ptr sdba = spot::remove_alternation(pvwaa, true);

    //_________________________________________________________________________________
    // Choosing the R

    // We go through all the states in C
    // In each one, we go through all its Q-s and build all possible R-s based on what types of states Q-s are
    // For each R - if it is a new R, we build an R-component
    //_________________________________________________________________________________


    unsigned nc = sdba->num_states(); //number of configurations C (states in the nondeterministic part)

    // State-names C are in style of "1,2,3", these represent states Q of the former VWAA configuration
    std::set<std::string> C[nc];

    auto sn = sdba->get_named_prop<std::vector<std::string>>("state-names");

    // We iterate over all states (C) of the automaton. ci = number of state C
    for (unsigned ci = 0; ci < nc; ++ci) {

        // We parse the statename ((*sn)[ci]) to create a set of states
        if (sn && ci < sn->size() && !(*sn)[ci].empty()) {
            std::string s = ((*sn)[ci]) + ",";
            std::string delimiter = ",";
            size_t pos = 0;
            std::string token;
            while ((pos = s.find(delimiter)) != std::string::npos) {
                token = s.substr(0, pos);
                C[ci].insert(token);
                s.erase(0, pos + delimiter.length());
            }
        } else {
            std::cout << "Wrong C state name."; // todo better error message
        }

        std::set<std::string> R;

        if (debug == "1"){std::cout << "\nChecking if this configuration contains only valid states: " << ci << "\n";}
        // Check if only states reachable from Qmays are in C. If not, this configuration can not contain an R.
        if (checkMayReachableStates(pvwaa, C[ci], R, isqmay)){  // We are using R just as a placeholder empty set here
            R.clear();
            if (debug == "1"){std::cout << "Yes! \n";}

            // We call this function to judge Q-s of this C and create R-s and R-components based on them
            createR(pvwaa, C[ci], C[ci], R, isqmay, isqmust, sdba, debug);
        }
    }

    return sdba;
}

// Conf = States Q we need to check
// Valid = States marked as QMay or their successors
bool checkMayReachableStates(std::shared_ptr<spot::twa_graph> vwaa, std::set<std::string> Conf,
                             std::set<std::string> Valid, bool isqmay[]){

    // We check each state whether it is Qmay. If it is, we add it to Valid with all successors
    for (auto q : Conf)
    {
        if (q.empty() || !isdigit(q.at(0))){
            if (q != "{}") {
                std::cout << "We are in BADSTATE: " << q << ". "; // todo Better error message
            }
            else {
                // This state is {} and can not be Qmay nor Qmust // todo Is this right?
            }
        } else {
            if (isqmay[std::stoi(q)]) {
                addToValid(vwaa, q, Valid);
            }
        }
    }

    // We check and return whether all states in Conf are valid (QMays and their successors)
    for (auto q : Conf)
    {
        if (!(Valid.find(q) != Valid.end())){
            return false;
        }
    }
    return true;
}

void addToValid(std::shared_ptr<spot::twa_graph> vwaa, std::string q, std::set<std::string> &Valid){
    Valid.insert(q);
    // We add into Valid all states reachable from q too
    for (auto &t: vwaa->out(std::stoi(q))) {
        for (unsigned d: vwaa->univ_dests(t.dst)) {
            // We exclude loops for effectivity, as they never need to be checked to be added again
            if (std::to_string(d) != q) {
                addToValid(vwaa, std::to_string(d), Valid);
            }
        }
    }
}

// Conf = The configuration C we are creating R for
// remaining = States Q (of the configuration C) that we still need to check
// Go through all states of Conf, check if they are qmay and qmust, add corresponding states of VWAA into R
void createR(std::shared_ptr<spot::twa_graph> vwaa, std::set<std::string> Conf, std::set<std::string> remaining, std::set<std::string> R,
             bool isqmay[], bool isqmust[], spot::twa_graph_ptr &sdba, std::string debug){

    // We choose first q that comes into way
    auto it = remaining.begin();
    std::string q;
    if (it != remaining.end()) q = *it;

    if (debug == "1"){std::cout << "We chose q: " << q;}
    // Erase it from remaining as we are checking it now
    remaining.erase(q);


    if (debug == "1"){std::cout << "Judging state: " << q << ". ";}
    // Checking state correctness
    if (q.empty() || !isdigit(q.at(0))){
        if (q != "{}") {
            std::cout << "We are in BADSTATE: " << q << ". "; // todo Deal with this
        }
        else {
            //If the state is {}, we don't have to check if it is Qmay or Qmust
            if (debug == "1"){std::cout << "q is {}. ";} // todo keep in mind acceptation
        }
    } else {
        // If this state is Qmust, we add it (and don't have to check Qmay)
        if (isqmust[std::stoi(q)]){
            if (debug == "1"){std::cout << "It is Qmust, adding to R. ";}
            if (R.count(q) == 0) {
                R.insert(q);
            }
        } else {
            // If it is Qmay, we recursively call the function and try both adding it and not
            if (isqmay[std::stoi(q)]){
                if (debug == "1"){std::cout << "It is Qmay, adding to R ";}

                // We create a new branch with new R and add the state q to this R
                std::set<std::string> Rx = R;
                if (Rx.count(q) == 0) {
                    Rx.insert(q);
                }

                if (!Conf.empty()){
                    // We run the branch building the R where this state is added
                    if (debug == "1"){std::cout << " and creating another branch for: " << q << ". ";}
                    createR(vwaa, Conf, remaining, Rx, isqmay, isqmust, sdba, debug);
                } else{
                    // If this was the last state, we have one R complete. Let's build an R-component from it.
                    if (debug == "1"){std::cout << " and this was last state, creating Rxcomp for: " << q << ". ";}
                    createRComp(Conf, Rx, sdba, debug);
                }
                // We also continue this run without adding this state to R - representing the second branch
                if (debug == "1"){std::cout<< "Also continuing for q " << q << ". ";}
            }
        }
        if (debug == "1"){std::cout << "Done checking may/must for q: " << q;}

}
    if (debug == "1"){std::cout << "\n Is this the last state? ";}
    // If this was the last state, we have this R complete. Let's build an R-component from it.
    if (remaining.empty()){
        if (debug == "1"){std::cout << " YES! Create R comp: \n";}
        createRComp(Conf, R, sdba, debug);
    } else{
        if (debug == "1"){std::cout << " NO! Check another state: \n";}
        createR(vwaa, Conf, remaining, R, isqmay, isqmust, sdba, debug);
    }

    return;
}

void createRComp(std::set<std::string> Conf, std::set<std::string> R, spot::twa_graph_ptr &sdba, std::string debug){

    // First we construct the edges from the first part into the R component

    if (debug == "1"){std::cout << " Start ";}
/*
    sdba->prop_universal()=false;
    // xz test: Add a state X into sdba
    sdba->new_state();
    bdd a = bdd_ithvar(sdba->register_ap("a"));
    sdba->new_edge(0, 2, a);

*/
    // im in one C. lets write what Qs are inside, or otherwise, lets print the name of this C:
    for (auto q : Conf){
        if (debug == "1"){std::cout << q << ", ";}
    }

    if (debug == "1"){std::cout << " End \n";}

    // todo For every edge going into R, "remove it" since it is accepting?
    // todo If the transition is looping on a state and it isn't going into F, we turn it into tt edge
    // todo We now construct the transitions from the phi1 and phi2 successors
    // todo We either only add edge, or we add it into acceptance transitions too
}





// todo try ltlcross to test this tool. generate random formulae and check them in ltlcross (using ltl2tgba) and this


/* Phis work
 * These should not be strings, but sets of states
// We will map two phi-s to each state so that it is in the form of (R, phi1, phi2)
std::map<unsigned, std::string> phi1;
std::map<unsigned, std::string> phi2;

for (unsigned c = 0; c < nc; ++c) {

    // We set the phis
    phi1[c] = "Phi_1";
    phi2[c] = "Phi_2"; //Change these two from strings to sets of states
}*/



/* xz Print from removing acceptance marks loop -------------
std::cout << "[" << spot::bdd_format_formula(dict, t.cond) << "] ";
bool notfirst = false;
for (unsigned d: pvwaa->univ_dests(t.dst))
{
    if (notfirst)
        std::cout << '&';
    else
        notfirst = true;
    std::cout << d;
}
std::cout << " " << t.acc << "\n";
// ---------------------------*/


/* Working with vwaa edges - notes
            xz t.cond is bdd of edges
            std::cout << "edge(" << t.src << " -> " << t.dst << "), label ";
            spot::bdd_print_formula(std::cout, dict, t.cond);
            auto edgelabel = spot::bdd_format_formula(dict, t.cond);
            std::cout << ", acc sets " << t.acc;
            std::cout << ", next succ " << (t.next_succ) << " Univ dests:\n";
            */



/* First version of iterating over states, not using spot
 *
    // We iterate over all states of the automaton, checking each one for its type (may, must)
    auto sets = aut->get_graph().states();
    //std::map<spot::twa_graph_state*, std::string> tuple; //maps a name to each state
    std::map<unsigned, std::string> statte; //maps a name to each state number

    int x = 0;

    for (unsigned i = 0; i < sets.size(); ++i) {
        auto triplet = (sets)[i];
        auto statedata = triplet.data();

        //from the state data we now evaluate the type(may, must, cant)
        statte[i] = "State name: " + std::to_string(i) + " (currently only number)";
        //tuple[&statedata] = "State name: " + std::to_string(i) + " (currently only number)"; // xz Instead, the state name should be assigned here

        //spot::twa::succ_iter(&statedata);


        //based on the type we now do one of the respective actions
        //
        auto succx = triplet.succ; // First outgoing edge (used when iterating)
        auto succy = triplet.succ_tail; // Last outgoing edge

        x++;
    }*/


/*
    // Changing from transition-based into state-based acceptance. Not an effective way, scrapping this.

    // Printing the automaton into helper with spot's -s option
    outs.open ("helper.hoa", std::ofstream::trunc);
    std::cout.rdbuf(outs.rdbuf());
    spot::print_hoa(std::cout, aut, "s");
    std::cout.rdbuf(coutbuf);
    outs.close();

    // Parsing the previous automaton from helper and printing it into helper2 with autfilt's -s (state-based) option
    std::system("autfilt helper.hoa -S -H > 'helper2.hoa'");   // xz name states?

    // Parsing the helper2 back, acquiring spot format again
    pvwaa = parse_aut("helper2.hoa", spot::make_bdd_dict());
    if (pvwaa->format_errors(std::cerr))
        return vwaa->spot_aut;  // xz returning random error, the file from printfile didnt create successfully?
    if (pvwaa->aborted)
    {
        std::cerr << "--ABORT-- read\n";
        return vwaa->spot_aut;  // xz returning random error, the file from printfile didnt create successfully?
    }
    aut = pvwaa->aut;
     */