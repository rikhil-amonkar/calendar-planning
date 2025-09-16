import z3
import json

def main():
    # Define the cities and their indices
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    n_cities = len(cities)
    n_days = 15

    # Map city names to indices
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    # Define the allowed direct flights as bidirectional edges
    edges = [
        (city_to_index['Helsinki'], city_to_index['Riga']),
        (city_to_index['Riga'], city_to_index['Tallinn']),
        (city_to_index['Vienna'], city_to_index['Helsinki']),
        (city_to_index['Riga'], city_to_index['Dublin']),
        (city_to_index['Vienna'], city_to_index['Riga']),
        (city_to_index['Reykjavik'], city_to_index['Vienna']),
        (city_to_index['Helsinki'], city_to_index['Dublin']),
        (city_to_index['Tallinn'], city_to_index['Dublin']),
        (city_to_index['Reykjavik'], city_to_index['Helsinki']),
        (city_to_index['Reykjavik'], city_to_index['Dublin']),
        (city_to_index['Helsinki'], city_to_index['Tallinn']),
        (city_to_index['Vienna'], city_to_index['Dublin'])
    ]
    allowed_edges_set = set()
    for (u, v) in edges:
        allowed_edges_set.add((u, v))
        allowed_edges_set.add((v, u))
    
    # Create Z3 variables
    start_city = z3.Int('start_city')
    loc = [z3.Int(f'loc_{i}') for i in range(n_days)]  # loc[i] is end city of day i+1
    flight_taken = [z3.Bool(f'flight_taken_{i}') for i in range(n_days)]  # flight_taken[i] is for day i+1
    
    solver = z3.Solver()
    
    # Constrain start_city and loc to be within valid city indices
    solver.add(start_city >= 0, start_city < n_cities)
    for i in range(n_days):
        solver.add(loc[i] >= 0, loc[i] < n_cities)
    
    # Day 1 constraints
    solver.add(z3.Implies(flight_taken[0], loc[0] != start_city))
    solver.add(z3.Implies(z3.Not(flight_taken[0]), loc[0] == start_city))
    # Flight on day1 must be an allowed edge
    solver.add(z3.Implies(flight_taken[0], 
                          z3.Or([z3.And(start_city == u, loc[0] == v) for (u, v) in allowed_edges_set])))
    
    # Constraints for days 2 to 15
    for i in range(1, n_days):
        # If flight taken, cities change; otherwise, same city
        solver.add(z3.Implies(flight_taken[i], loc[i] != loc[i-1]))
        solver.add(z3.Implies(z3.Not(flight_taken[i]), loc[i] == loc[i-1]))
        # Flight must be on an allowed edge
        solver.add(z3.Implies(flight_taken[i], 
                              z3.Or([z3.And(loc[i-1] == u, loc[i] == v) for (u, v) in allowed_edges_set])))
    
    # Total days in each city
    total_days = [0] * n_cities
    for c in range(n_cities):
        # For day 1
        in_day1 = z3.Or(start_city == c, z3.And(flight_taken[0], loc[0] == c))
        in_days = [in_day1]
        # For days 2 to 15
        for i in range(1, n_days):
            in_day = z3.Or(loc[i] == c, z3.And(flight_taken[i], loc[i-1] == c))
            in_days.append(in_day)
        # Sum the days for city c
        total_days[c] = sum([z3.If(cond, 1, 0) for cond in in_days])
    
    # Add duration constraints
    solver.add(total_days[city_to_index['Dublin']] == 5)
    solver.add(total_days[city_to_index['Helsinki']] == 3)
    solver.add(total_days[city_to_index['Riga']] == 3)
    solver.add(total_days[city_to_index['Reykjavik']] == 2)
    solver.add(total_days[city_to_index['Vienna']] == 2)
    solver.add(total_days[city_to_index['Tallinn']] == 5)
    
    # Event constraints
    # Helsinki: at least one day in [3,5] (days 3,4,5)
    day3_hel = z3.Or(loc[2] == city_to_index['Helsinki'], z3.And(flight_taken[2], loc[1] == city_to_index['Helsinki']))
    day4_hel = z3.Or(loc[3] == city_to_index['Helsinki'], z3.And(flight_taken[3], loc[2] == city_to_index['Helsinki']))
    day5_hel = z3.Or(loc[4] == city_to_index['Helsinki'], z3.And(flight_taken[4], loc[3] == city_to_index['Helsinki']))
    solver.add(z3.Or(day3_hel, day4_hel, day5_hel))
    
    # Vienna: must be in Vienna on day2 and day3
    day2_vie = z3.Or(loc[1] == city_to_index['Vienna'], z3.And(flight_taken[1], loc[0] == city_to_index['Vienna']))
    day3_vie = z3.Or(loc[2] == city_to_index['Vienna'], z3.And(flight_taken[2], loc[1] == city_to_index['Vienna']))
    solver.add(day2_vie, day3_vie)
    
    # Tallinn: at least one day in [7,11] (days 7 to 11)
    tallinn_days = []
    for d in [6,7,8,9,10]:  # days 7 to 11 (indices 6 to 10 in 0-indexed days)
        in_day = z3.Or(loc[d] == city_to_index['Tallinn'], z3.And(flight_taken[d], loc[d-1] == city_to_index['Tallinn']))
        tallinn_days.append(in_day)
    solver.add(z3.Or(tallinn_days))
    
    # Solve the problem
    if solver.check() == z3.sat:
        model = solver.model()
        start_city_val = model.evaluate(start_city).as_long()
        loc_vals = [model.evaluate(loc[i]).as_long() for i in range(n_days)]
        flight_taken_vals = [model.evaluate(flight_taken[i]) for i in range(n_days)]
        
        # Build itinerary
        itinerary = []
        # Day 1
        day1_cities = [start_city_val]
        if flight_taken_vals[0] and loc_vals[0] != start_city_val:
            day1_cities.append(loc_vals[0])
        for c in day1_cities:
            itinerary.append({"day": 1, "place": cities[c]})
        
        # Days 2 to 15
        for d in range(2, n_days+1):
            day_cities = [loc_vals[d-1]]
            if flight_taken_vals[d-1] and loc_vals[d-2] != loc_vals[d-1]:
                day_cities.append(loc_vals[d-2])
            for c in day_cities:
                itinerary.append({"day": d, "place": cities[c]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()