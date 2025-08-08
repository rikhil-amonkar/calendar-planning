from z3 import *
import json

def main():
    s = [Int('s%d' % i) for i in range(0, 17)]
    cities = {0: "Bucharest", 1: "Lyon", 2: "Porto"}
    solver = Solver()
    
    # Each s_i must be in {0,1,2}
    for i in range(0, 17):
        solver.add(And(s[i] >= 0, s[i] <= 2))
    
    # Flight constraints: only direct flights allowed
    for i in range(1, 17):
        prev = s[i-1]
        curr = s[i]
        flight_cond = Or(
            And(prev == 0, curr == 1),
            And(prev == 1, curr == 0),
            And(prev == 1, curr == 2),
            And(prev == 2, curr == 1)
        )
        solver.add(If(prev != curr, flight_cond, True))
    
    # Bucharest days: part1 (start days) + part2 (flight arrivals)
    part1_b = Sum([If(s[i] == 0, 1, 0) for i in range(0, 16)])
    part2_b = Sum([If(And(s[i] == 0, s[i] != s[i-1]), 1, 0) for i in range(1, 17)])
    b_days = part1_b + part2_b
    solver.add(b_days == 7)
    
    # Lyon days
    part1_l = Sum([If(s[i] == 1, 1, 0) for i in range(0, 16)])
    part2_l = Sum([If(And(s[i] == 1, s[i] != s[i-1]), 1, 0) for i in range(1, 17)])
    l_days = part1_l + part2_l
    solver.add(l_days == 7)
    
    # Porto days
    part1_p = Sum([If(s[i] == 2, 1, 0) for i in range(0, 16)])
    part2_p = Sum([If(And(s[i] == 2, s[i] != s[i-1]), 1, 0) for i in range(1, 17)])
    p_days = part1_p + part2_p
    solver.add(p_days == 4)
    
    # Wedding constraint: at least one day in Bucharest between day1 and day7 (s0 to s7)
    solver.add(Or([s[i] == 0 for i in range(0, 8)]))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        s_vals = [model.evaluate(s[i]).as_long() for i in range(0, 17)]
        itinerary = []
        for day in range(1, 17):
            start_city_val = s_vals[day-1]
            end_city_val = s_vals[day]
            if start_city_val == end_city_val:
                place_str = cities[start_city_val]
            else:
                place_str = cities[start_city_val] + " and " + cities[end_city_val]
            itinerary.append({"day": day, "place": place_str})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()