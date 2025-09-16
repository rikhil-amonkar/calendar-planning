from z3 import *
import json

def main():
    # City encoding: Milan=0, Seville=1, Naples=2
    Milan, Seville, Naples = 0, 1, 2
    
    s0 = Int('s0')
    e = [Int('e_%d' % i) for i in range(1, 13)]
    s = [Int('s_%d' % i) for i in range(1, 13)]
    
    solver = Solver()
    
    # s0 must be Milan or Naples (not Seville)
    solver.add(Or(s0 == Milan, s0 == Naples))
    
    # Define s_i for each day: s1 = s0, s_i = e_{i-1} for i>1
    for i in range(1, 13):
        if i == 1:
            solver.add(s[i-1] == s0)
        else:
            solver.add(s[i-1] == e[i-2])
    
    # Days 1-8: no Seville at start or end
    for i in range(1, 9):
        solver.add(s[i-1] != Seville)
        solver.add(e[i-1] != Seville)
    
    # Days 9-12: must have Seville at start or end
    for i in range(9, 13):
        solver.add(Or(s[i-1] == Seville, e[i-1] == Seville))
    
    # Flight constraints
    for i in range(1, 13):
        flight_cond = (s[i-1] != e[i-1])
        allowed_flights = Or(
            And(s[i-1] == Milan, e[i-1] == Seville),
            And(s[i-1] == Seville, e[i-1] == Milan),
            And(s[i-1] == Milan, e[i-1] == Naples),
            And(s[i-1] == Naples, e[i-1] == Milan)
        )
        solver.add(Implies(flight_cond, allowed_flights))
    
    # Total days in each city
    milan_days = 0
    seville_days = 0
    naples_days = 0
    for i in range(1, 13):
        milan_days += If(Or(s[i-1] == Milan, e[i-1] == Milan), 1, 0)
        seville_days += If(Or(s[i-1] == Seville, e[i-1] == Seville), 1, 0)
        naples_days += If(Or(s[i-1] == Naples, e[i-1] == Naples), 1, 0)
    
    solver.add(milan_days == 7)
    solver.add(seville_days == 4)
    solver.add(naples_days == 3)
    
    # Total flight days must be 2
    flight_days = Sum([If(s[i-1] != e[i-1], 1, 0) for i in range(1, 13)])
    solver.add(flight_days == 2)
    
    # Additional constraints to ensure exactly one flight during days 1-8 and one during days 9-12
    flight_days_in_1_8 = Sum([If(s[i] != e[i], 1, 0) for i in range(0, 8)])
    flight_days_in_9_12 = Sum([If(s[i] != e[i], 1, 0) for i in range(8, 12)])
    solver.add(flight_days_in_1_8 == 1)
    solver.add(flight_days_in_9_12 == 1)
    
    # The flight during days 9-12 must be on day 9 (since day9 must start non-Seville and end in Seville)
    solver.add(e[8] == Seville)  # End of day9 must be Seville
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        e_vals = [model[e_i].as_long() for e_i in e]
        
        # Group consecutive days with the same ending city
        runs = []
        i = 0
        n = 12
        while i < n:
            j = i
            while j < n and e_vals[j] == e_vals[i]:
                j += 1
            start_day = i + 1
            end_day = j
            runs.append((start_day, end_day, e_vals[i]))
            i = j
        
        # Format the itinerary
        itinerary = []
        city_map = {Milan: "Milan", Seville: "Seville", Naples: "Naples"}
        for (start, end, city_idx) in runs:
            if start == end:
                day_range = "Day %d" % start
            else:
                day_range = "Day %d-%d" % (start, end)
            itinerary.append({'day_range': day_range, 'place': city_map[city_idx]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()