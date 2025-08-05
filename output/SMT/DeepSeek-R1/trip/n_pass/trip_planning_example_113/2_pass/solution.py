from z3 import *
import json

def main():
    # Define the city mappings
    Milan = 0
    Seville = 1
    Naples = 2
    
    s0 = Int('s0')
    e = [Int('e_%d' % i) for i in range(1, 13)]
    
    solver = Solver()
    
    # s0 must be either Milan or Naples (not Seville)
    solver.add(Or(s0 == Milan, s0 == Naples))
    for i in range(12):
        solver.add(e[i] >= 0, e[i] <= 2)
    
    # For days 1 to 8: not in Seville
    for i in range(1, 9):
        # s_i: start of day i
        if i == 1:
            s_i = s0
        else:
            s_i = e[i-2]  # because e[0] is for day1, so for day2: s2 = e0 (index0 in e)
        # Constraint: both start and end of day i not Seville
        solver.add(s_i != Seville)
        solver.add(e[i-1] != Seville)
    
    # For days 9 to 12: must be in Seville (either start or end)
    for i in range(9, 13):
        if i == 1:
            s_i = s0
        else:
            s_i = e[i-2]
        solver.add(Or(s_i == Seville, e[i-1] == Seville))
    
    # Flight constraints
    for i in range(1, 13):
        if i == 1:
            s_i = s0
        else:
            s_i = e[i-2]
        end_i = e[i-1]
        # If there is a flight (s_i != end_i), then it must be an allowed flight
        flight_cond = (s_i != end_i)
        allowed_flights = Or(
            And(s_i == Milan, end_i == Seville),
            And(s_i == Seville, end_i == Milan),
            And(s_i == Milan, end_i == Naples),
            And(s_i == Naples, end_i == Milan)
        )
        solver.add(Implies(flight_cond, allowed_flights))
    
    # Total days for Naples and Milan
    total_naples = 0
    total_milan = 0
    for i in range(1, 13):
        if i == 1:
            s_i = s0
        else:
            s_i = e[i-2]
        end_i = e[i-1]
        # For Naples: count if start or end is Naples
        total_naples += If(Or(s_i == Naples, end_i == Naples), 1, 0)
        # For Milan: count if start or end is Milan
        total_milan += If(Or(s_i == Milan, end_i == Milan), 1, 0)
    
    solver.add(total_naples == 3)
    solver.add(total_milan == 7)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        s0_val = model[s0].as_long()
        e_vals = [model[e_i].as_long() for e_i in e]
        
        # Map to city names
        city_map = {Milan: "Milan", Seville: "Seville", Naples: "Naples"}
        itinerary = []
        for day in range(1, 13):
            city_index = e_vals[day-1]
            city_name = city_map[city_index]
            itinerary.append({"day": day, "city": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()