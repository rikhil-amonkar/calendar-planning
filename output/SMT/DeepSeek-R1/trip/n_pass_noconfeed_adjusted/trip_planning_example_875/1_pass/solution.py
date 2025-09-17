import z3
import json

def main():
    # Cities and their required stays
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    stays = {
        'Stuttgart': 3,
        'Edinburgh': 4,
        'Athens': 4,
        'Split': 2,
        'Krakow': 4,
        'Venice': 5,
        'Mykonos': 4
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Krakow', 'Split'),
        ('Split', 'Athens'),
        ('Edinburgh', 'Krakow'),
        ('Venice', 'Stuttgart'),
        ('Krakow', 'Stuttgart'),
        ('Edinburgh', 'Stuttgart'),
        ('Stuttgart', 'Athens'),
        ('Venice', 'Edinburgh'),
        ('Athens', 'Mykonos'),
        ('Venice', 'Athens'),
        ('Stuttgart', 'Split'),
        ('Edinburgh', 'Athens')
    ]
    
    # Create symmetric direct flights
    symmetric_flights = set()
    for (a, b) in direct_flights:
        symmetric_flights.add((a, b))
        symmetric_flights.add((b, a))
    
    # Initialize solver
    solver = z3.Solver()
    
    # Create a 2D array of variables: days 1..20, each day has a boolean for each city
    x = {}
    for day in range(1, 21):
        for city in cities:
            x[(day, city)] = z3.Bool(f"day_{day}_{city}")
    
    # Constraint: Each day has at least one city and at most two cities
    for day in range(1, 21):
        city_vars = [x[(day, c)] for c in cities]
        solver.add(z3.AtLeast(*city_vars, 1))
        solver.add(z3.AtMost(*city_vars, 2))
        
        # For each pair of distinct cities, if both are true then they must be connected by a direct flight
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in symmetric_flights:
                    solver.add(z3.Not(z3.And(x[(day, c1)], x[(day, c2)])))
    
    # Constraint: Total days per city must match the required stays
    for city in cities:
        total = z3.Sum([z3.If(x[(day, city)], 1, 0) for day in range(1, 21)])
        solver.add(total == stays[city])
    
    # Connectivity constraints between consecutive days
    for day in range(1, 20):
        for city in cities:
            # If city is present on day but not on day+1, then there must be a connected city present on both days
            condition1 = z3.And(x[(day, city)], z3.Not(x[(day+1, city)]))
            possible_connections1 = []
            for other in cities:
                if other != city and (city, other) in symmetric_flights:
                    possible_connections1.append(z3.And(x[(day, other)], x[(day+1, other)]))
            solver.add(z3.Implies(condition1, z3.Or(possible_connections1)))
            
            # If city is present on day+1 but not on day, then there must be a connected city present on both days
            condition2 = z3.And(z3.Not(x[(day, city)]), x[(day+1, city)])
            possible_connections2 = []
            for other in cities:
                if other != city and (city, other) in symmetric_flights:
                    possible_connections2.append(z3.And(x[(day, other)], x[(day+1, other)]))
            solver.add(z3.Implies(condition2, z3.Or(possible_connections2)))
    
    # Event constraints
    # Stuttgart between day 11 and 13
    stuttgart_constraint = z3.Or([x[(d, 'Stuttgart')] for d in [11, 12, 13]])
    solver.add(stuttgart_constraint)
    
    # Split between day 13 and 14
    split_constraint = z3.Or([x[(d, 'Split')] for d in [13, 14]])
    solver.add(split_constraint)
    
    # Krakow between day 8 and 11
    krakow_constraint = z3.Or([x[(d, 'Krakow')] for d in [8, 9, 10, 11]])
    solver.add(krakow_constraint)
    
    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract the daily assignments
        daily_assignments = {}
        for day in range(1, 21):
            cities_on_day = []
            for city in cities:
                if z3.is_true(model.eval(x[(day, city)])):
                    cities_on_day.append(city)
            daily_assignments[day] = sorted(cities_on_day)
        
        # Group consecutive days with the same assignment
        itinerary_segments = []
        start_day = 1
        current_assignment = daily_assignments[1]
        for day in range(2, 21):
            if daily_assignments[day] == current_assignment:
                continue
            else:
                end_day = day - 1
                segment_str = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                place_str = " and ".join(current_assignment)
                itinerary_segments.append({"day_range": segment_str, "place": place_str})
                start_day = day
                current_assignment = daily_assignments[day]
        # Add the last segment
        end_day = 20
        segment_str = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
        place_str = " and ".join(current_assignment)
        itinerary_segments.append({"day_range": segment_str, "place": place_str})
        
        # Output as JSON
        result = {"itinerary": itinerary_segments}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()