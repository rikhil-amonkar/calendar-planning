import z3

def main():
    # Define cities and their indices
    cities = ['Madrid', 'Paris', 'Bucharest', 'Seville']
    n_days = 15
    n_cities = len(cities)
    
    # Direct flights as tuples of indices (bidirectional)
    direct_flights = [
        ('Paris', 'Bucharest'),
        ('Seville', 'Paris'),
        ('Madrid', 'Bucharest'),
        ('Madrid', 'Paris'),
        ('Madrid', 'Seville')
    ]
    # Convert to set of integer pairs
    direct_flights_set = set()
    for a, b in direct_flights:
        i = cities.index(a)
        j = cities.index(b)
        direct_flights_set.add((i, j))
        direct_flights_set.add((j, i))
    
    # Z3 variables
    start_city = [z3.Int('start_city_%d' % d) for d in range(1, n_days+1)]
    flight = [z3.Bool('flight_%d' % d) for d in range(1, n_days)]
    to_city = [z3.Int('to_city_%d' % d) for d in range(1, n_days)]
    
    solver = z3.Solver()
    
    # Constraint: Start in Madrid (day1)
    solver.add(start_city[0] == 0)
    
    # Constraints for each day: start_city within valid range
    for d in range(n_days):
        solver.add(z3.Or([start_city[d] == i for i in range(n_cities)]))
    
    # Constraints for flights and to_city
    for d in range(n_days-1):  # d from 0 to 13 (for flights on day d+1)
        # If flight[d] is True, then to_city[d] must be a neighbor of start_city[d] and not the same
        options = []
        for (i, j) in direct_flights_set:
            if i != j:
                options.append(z3.And(start_city[d] == i, to_city[d] == j))
        solver.add(z3.Implies(flight[d], z3.Or(options)))
        solver.add(z3.Implies(flight[d], start_city[d] != to_city[d]))
        # Next day's start_city: if flight, then to_city; else same as current
        solver.add(z3.If(flight[d], start_city[d+1] == to_city[d], start_city[d+1] == start_city[d]))
    
    # Constraints for total days in each city
    total_days = [0] * n_cities
    for i in range(n_cities):
        # Count days where the start_city is i
        start_count = z3.Sum([z3.If(start_city[d] == i, 1, 0) for d in range(n_days)])
        # Count days where the flight arrives at i (for flights on day d+1, which is flight[d] and to_city[d]==i)
        flight_arrival_count = z3.Sum([z3.If(z3.And(flight[d], to_city[d] == i), 1, 0) for d in range(n_days-1)])
        total_days[i] = start_count + flight_arrival_count
    # Required days: Madrid:7, Paris:6, Bucharest:2, Seville:3
    solver.add(total_days[0] == 7)  # Madrid
    solver.add(total_days[1] == 6)  # Paris
    solver.add(total_days[2] == 2)  # Bucharest
    solver.add(total_days[3] == 3)  # Seville
    
    # Constraints: Madrid on days 1-7
    for d in range(7):  # days 1-7: indices 0 to 6
        solver.add(z3.Or(start_city[d] == 0, z3.And(flight[d], to_city[d] == 0)))
    
    # Constraints: Bucharest on days 14 and 15
    # Day14: index13
    solver.add(z3.Or(start_city[13] == 2, z3.And(flight[13], to_city[13] == 2)))
    # Day15: index14 (no flight on day15)
    solver.add(start_city[14] == 2)
    
    # Solve
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract values
        start_city_val = []
        for d in range(n_days):
            val = model.evaluate(start_city[d])
            start_city_val.append(val.as_long())
        
        flight_val = []
        for d in range(n_days-1):
            val = model.evaluate(flight[d])
            flight_val.append(val.is_true())
        
        to_city_val = []
        for d in range(n_days-1):
            val = model.evaluate(to_city[d])
            to_city_val.append(val.as_long())
        
        # Generate continuous stays
        continuous_stays = []
        current_city = start_city_val[0]
        start_day = 1
        for d in range(n_days-1):  # d from 0 to 13 (for flights on day d+1)
            if flight_val[d]:
                end_day = d+1  # flight on day d+1, so current stay ends at day d+1
                continuous_stays.append((start_day, end_day, current_city))
                current_city = to_city_val[d]
                start_day = end_day  # new stay starts on the same day (flight day)
        continuous_stays.append((start_day, n_days, current_city))
        
        # Format day range
        def format_days(s, e):
            if s == e:
                return "Day %d" % s
            else:
                return "Day %d-%d" % (s, e)
        
        # Build itinerary
        itinerary = []
        for (s, e, c) in continuous_stays:
            day_range_str = format_days(s, e)
            itinerary.append({"day_range": day_range_str, "place": cities[c]})
            if e < n_days:  # if not the last day, check if there was a flight on day e
                # Flight on day e: flight_val[e-1] is the flight on day e (since flight index 0 is day1)
                if e-1 < len(flight_val) and flight_val[e-1]:
                    dep_city_idx = start_city_val[e-1]
                    arr_city_idx = to_city_val[e-1]
                    itinerary.append({"day_range": format_days(e, e), "place": cities[dep_city_idx]})
                    itinerary.append({"day_range": format_days(e, e), "place": cities[arr_city_idx]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()