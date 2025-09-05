#!/usr/bin/env python3
import json
from z3 import *

def main():
    # Trip parameters
    total_days = 12
    dublin_required = 2
    riga_required = 5
    vilnius_required = 7

    # Create a Z3 solver instance
    solver = Solver()

    # Define SMT integer variables for the flight days.
    # dublin_dep: the day on which we fly from Dublin to Riga (last day in Dublin)
    # riga_dep: the day on which we fly from Riga to Vilnius (last day in Riga)
    dublin_dep = Int("dublin_dep")
    riga_dep = Int("riga_dep")

    # Boundaries for the flight days.
    solver.add(dublin_dep >= 1, dublin_dep <= total_days)
    solver.add(riga_dep >= dublin_dep, riga_dep <= total_days)

    # The itinerary is structured as follows:
    # - Dublin: from day 1 to dublin_dep (inclusive)
    # - Riga: from day dublin_dep to riga_dep (inclusive)
    # - Vilnius: from day riga_dep to total_days (inclusive)
    # Note: If a flight occurs on a day, that day is counted in both the city of departure and arrival.
    
    # Constraint for Dublin: duration = (dublin_dep - 1 + 1) = dublin_dep must equal the required days in Dublin.
    solver.add(dublin_dep == dublin_required)
    # Constraint for Riga: duration = (riga_dep - dublin_dep + 1) must equal the required days in Riga.
    solver.add(riga_dep - dublin_dep + 1 == riga_required)
    # Constraint for Vilnius: duration = (total_days - riga_dep + 1) must equal the required days in Vilnius.
    solver.add(total_days - riga_dep + 1 == vilnius_required)

    # The direct flight connections (for reference):
    # Dublin <-> Riga and Riga -> Vilnius. Our itinerary uses Dublin -> Riga -> Vilnius.
    
    if solver.check() == sat:
        model = solver.model()
        # Extract the solved flight days
        dp = model[dublin_dep].as_long()   # Last day in Dublin (and flight day to Riga)
        rp = model[riga_dep].as_long()       # Last day in Riga (and flight day to Vilnius)

        itinerary = [
            {"day_range": f"Day 1-{dp}", "place": "Dublin"},
            {"day_range": f"Day {dp}-{rp}", "place": "Riga"},
            {"day_range": f"Day {rp}-{total_days}", "place": "Vilnius"}
        ]
        result = {"itinerary": itinerary}
    else:
        result = {"error": "No valid itinerary found."}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()