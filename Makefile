#    Copyright (c) 2016 Juraj Major
#    Copyright (c) 2018 Michal Románek
#
#    This file is part of LTL2SDBA.
#
#    LTL2SDBA is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 3 of the License, or
#    (at your option) any later version.
#
#    LTL2SDBA is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with LTL2SDBA.  If not, see <http://www.gnu.org/licenses/>.

FILES = alternating.cpp semideterministic.cpp automaton.cpp utils.cpp main.cpp

ltl2sdba: $(FILES)
	g++ -std=c++14 -o ltl2sdba $(FILES) -lspot -lbddx

clean:
	rm ltl2sdba
