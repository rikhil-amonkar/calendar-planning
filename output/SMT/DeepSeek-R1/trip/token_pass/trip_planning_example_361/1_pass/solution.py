import json
from z3 import *

def main():
    # Cities
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    n_days = 15
    
    # Adjacency list
    adjacent = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Madrid': ['Bucharest', 'Paris', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    # Initialize Z3 arrays for each city per day
    P = [Bool(f"P_{i}") for i in range(1, n_days+1)]
    M = [Bool(f"M_{i}") for i in range(1, n_days+1)]
    B = [Bool(f"B_{i}") for i in range(1, n_days+1)]
    S = [Bool(f"S_{i}") for i in range(1, n_days+1)]
    city_vars = {'Paris': P, 'Madrid': M, 'Bucharest': B, 'Seville': S}
    
    solver = Solver()
    
    # Fixed constraints: Madrid on days 1-7, Bucharest on days 14-15
    for i in range(1, 8):
        solver.add(M[i-1])
    for i in range(14, 16):
        solver.add(B[i-1])
    
    # Total days constraints
    solver.add(Sum([If(P[i], 1, 0) for i in range(n_days)]) == 6)
    solver.add(Sum([If(M[i], 1, 0) for i in range(n_days)]) == 7)
    solver.add(Sum([If(B[i], 1, 0) for i in range(n_days)]) == 2)
    solver.add(Sum([If(S[i], 1, 0) for i in range(n_days)]) == 3)
    
    # For each day: at least one city, at most two cities
    for i in range(n_days):
        day_cities = [P[i], M[i], B[i], S[i]]
        solver.add(Or(day_cities))
        solver.add(AtMost(*day_cities, 2))
        
        # If two cities on a day, they must be adjacent
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    if c2 not in adjacent[c1]:
                        solver.add(Not(And(city_vars[c1][i], city_vars[c2][i])))
    
    # Connectivity between consecutive days
    for i in range(n_days-1):
        current_day = [P[i], M[i], B[i], S[i]]
        next_day = [P[i+1], M[i+1], B[i+1], S[i+1]]
        
        # For each city in next day not in current day, it must be adjacent to some city in current day
        for c in cities:
            next_city = city_vars[c][i+1]
            current_city = city_vars[c][i]
            other_cities = [city for city in cities if city != c]
            # If city appears in next day but not current day, it must be adjacent to at least one city in current day
            adj_constraint = Or([And(city_vars[other][i], Bool(f"{other}_{c}" in adjacent[other])) for other in other_cities])
            solver.add(Implies(And(next_city, Not(current_city)), adj_constraint))
        
        # At most one new city per day
        new_cities = []
        for c in cities:
            current_city = city_vars[c][i]
            next_city = city_vars[c][i+1]
            new_cities.append(And(next_city, Not(current_city)))
        solver.add(AtMost(*new_cities, 1))
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_set = None
        start_day = 1
        day_assignments = []
        
        # Determine the set of cities for each day from the model
        for i in range(n_days):
            day_cities = []
            for city in cities:
                if is_true(model.eval(city_vars[city][i])):
                    day_cities.append(city)
            day_assignments.append(day_cities)
        
        # Group consecutive days with the same set of cities
        for i in range(n_days):
            current_day_set = day_assignments[i]
            if current_set is None:
                current_set = current_day_set
                start_day = i+1
            else:
                if current_day_set != current_set:
                    place_str = " and ".join(current_set)
                    day_range = f"Day {start_day}-{i}" if start_day != i else f"Day {start_day}"
                    itinerary.append({"day_range": day_range, "place": place_str})
                    current_set = current_day_set
                    start_day = i+1
        # Add the last segment
        place_str = " and ".join(current_set)
        day_range = f"Day {start_day}-{n_days}" if start_day != n_days else f"Day {start_day}"
        itinerary.append({"day_range": day_range, "place": place_str})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()