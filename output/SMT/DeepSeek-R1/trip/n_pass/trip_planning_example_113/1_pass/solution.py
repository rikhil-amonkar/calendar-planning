from z3 import *
import json

def main():
    s0 = Int('s0')
    end = [Int('end_%d' % i) for i in range(1, 13)]
    
    solver = Solver()
    
    # Define possible cities: 0=Milan, 1=Seville, 2=Naples
    solver.add(s0 >= 0, s0 <= 2)
    for i in range(12):
        solver.add(end[i] >= 0, end[i] <= 2)
    
    # Seville constraints: not in Seville on start or days 1-8, and in Seville on days 9-12
    solver.add(s0 != 1)  # s0 not Seville
    for i in range(8):    # days 1-8: end[0] to end[7]
        solver.add(end[i] != 1)
    for i in range(8, 12): # days 9-12: end[8] to end[11]
        solver.add(end[i] == 1)
    
    # Flight constraints for day 1: if s0 != end[0], then must be a direct flight
    flight1_cond = (s0 != end[0])
    flight1_allowed = Or(
        And(s0 == 0, end[0] == 1),
        And(s0 == 1, end[0] == 0),
        And(s0 == 2, end[0] == 0),
        And(s0 == 0, end[0] == 2)
    )
    solver.add(Implies(flight1_cond, flight1_allowed))
    
    # Flight constraints for days 2 to 12
    for idx in range(1, 12):  # idx from 1 to 11: representing flight on day idx+1
        prev = end[idx-1]
        curr = end[idx]
        flight_cond = (prev != curr)
        flight_allowed = Or(
            And(prev == 0, curr == 1),
            And(prev == 1, curr == 0),
            And(prev == 2, curr == 0),
            And(prev == 0, curr == 2)
        )
        solver.add(Implies(flight_cond, flight_allowed))
    
    # Total days in Milan (0)
    total_milan = If(Or(s0 == 0, end[0] == 0), 1, 0)
    for idx in range(0, 11):  # for gaps: 0 to 10, 11 gaps for 12 days
        total_milan += If(Or(end[idx] == 0, end[idx+1] == 0), 1, 0)
    solver.add(total_milan == 7)
    
    # Total days in Naples (2)
    total_naples = If(Or(s0 == 2, end[0] == 2), 1, 0)
    for idx in range(0, 11):
        total_naples += If(Or(end[idx] == 2, end[idx+1] == 2), 1, 0)
    solver.add(total_naples == 3)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        s0_val = model[s0].as_long()
        end_vals = [model[end[i]].as_long() for i in range(12)]
        
        cities = {0: "Milan", 1: "Seville", 2: "Naples"}
        itinerary_list = []
        for day in range(1, 13):
            city_index = end_vals[day-1]
            city_name = cities[city_index]
            itinerary_list.append({"day": day, "city": city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()