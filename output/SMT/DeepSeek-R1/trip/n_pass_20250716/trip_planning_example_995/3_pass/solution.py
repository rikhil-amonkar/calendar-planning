from z3 import *
import json

def main():
    # Define the city mapping
    cities = {
        'Barcelona': 0,
        'Stuttgart': 1,
        'Venice': 2,
        'Split': 3,
        'Brussels': 4,
        'Copenhagen': 5,
        'Oslo': 6
    }
    
    # Reverse mapping for output
    city_names = {v: k for k, v in cities.items()}
    
    # Required days per city (by index)
    req_days_list = [3, 3, 4, 4, 3, 3, 2]  # [0: Barcelona, 1: Stuttgart, 2: Venice, 3: Split, 4: Brussels, 5: Copenhagen, 6: Oslo]
    
    # Undirected edges
    edges_list = [
        (0,1), (0,2), (0,3), (0,4), (0,5), (0,6),
        (1,2), (1,3), (1,5),
        (2,4), (2,5), (2,6),
        (3,5), (3,6),
        (4,5), (4,6),
        (5,6)
    ]
    
    n = 7  # number of cities
    
    # Create Z3 variables
    c = [Int(f'c_{i}') for i in range(n)]  # city sequence
    s = [Int(f's_{i}') for i in range(n)]  # start days
    e = [Int(f'e_{i}') for i in range(n)]  # end days
    
    solver = Solver()
    
    # Fix the first city as Barcelona
    solver.add(c[0] == 0)
    
    # All cities are distinct and in the range [0,6]
    solver.add(Distinct(c))
    for i in range(n):
        solver.add(c[i] >= 0, c[i] <= 6)
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(n-1):
        conds = []
        for edge in edges_list:
            a, b = edge
            conds.append(Or(
                And(c[i] == a, c[i+1] == b),
                And(c[i] == b, c[i+1] == a)
            ))
        solver.add(Or(conds))
    
    # Day constraints
    solver.add(s[0] == 1)  # Barcelona starts on day 1
    solver.add(e[0] == 3)  # Barcelona ends on day 3
    
    # For each subsequent city, start day is the end day of the previous city
    for i in range(1, n):
        solver.add(s[i] == e[i-1])
    
    # The last city ends on day 16
    solver.add(e[n-1] == 16)
    
    # Length of stay for each city: end - start + 1 = required days
    for i in range(n):
        expr = req_days_list[6]  # default for Oslo (6)
        for j in range(5, -1, -1):
            expr = If(c[i] == j, req_days_list[j], expr)
        solver.add(e[i] - s[i] + 1 == expr)
    
    # Constraints for Oslo (city 6) and Brussels (city 4)
    oslo_constraints = []
    brussels_constraints = []
    for i in range(n):
        # Oslo must cover days 3 and 4: stay must start<=3 and end>=4
        oslo_constraints.append(And(c[i] == 6, s[i] <= 3, e[i] >= 4))
        # Brussels must cover days 9,10,11: stay must start<=9 and end>=11
        brussels_constraints.append(And(c[i] == 4, s[i] <= 9, e[i] >= 11))
    solver.add(Or(oslo_constraints))
    solver.add(Or(brussels_constraints))
    
    # Ensure days are within bounds
    for i in range(n):
        solver.add(s[i] >= 1, s[i] <= 16)
        solver.add(e[i] >= 1, e[i] <= 16)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        c_val = [model.evaluate(c[i]).as_long() for i in range(n)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(n)]
        e_val = [model.evaluate(e[i]).as_long() for i in range(n)]
        
        # Build itinerary
        itinerary = []
        
        # First city: entire block
        start0 = s_val[0]
        end0 = e_val[0]
        if start0 == end0:
            day_str0 = f"Day {start0}"
        else:
            day_str0 = f"Day {start0}-{end0}"
        itinerary.append({"day_range": day_str0, "place": city_names[c_val[0]]})
        
        # Subsequent cities: flight records and entire blocks
        for i in range(0, n-1):
            flight_day = e_val[i]  # same as s_val[i+1]
            # Departure from current city
            itinerary.append({"day_range": f"Day {flight_day}", "place": city_names[c_val[i]]})
            # Arrival at next city
            itinerary.append({"day_range": f"Day {flight_day}", "place": city_names[c_val[i+1]]})
            
            # Entire block for next city
            start_next = s_val[i+1]
            end_next = e_val[i+1]
            if start_next == end_next:
                day_str_next = f"Day {start_next}"
            else:
                day_str_next = f"Day {start_next}-{end_next}"
            itinerary.append({"day_range": day_str_next, "place": city_names[c_val[i+1]]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()