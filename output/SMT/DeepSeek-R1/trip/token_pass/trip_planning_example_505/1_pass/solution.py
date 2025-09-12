import z3
import json

def main():
    # Cities and days
    cities = ['P', 'S', 'Sp', 'K', 'F']
    n_days = 8
    city_names = {
        'P': 'Prague',
        'S': 'Stuttgart',
        'Sp': 'Split',
        'K': 'Krakow',
        'F': 'Florence'
    }
    
    # Create Z3 variables for each city and day
    in_vars = {}
    for c in cities:
        for i in range(1, n_days + 1):
            in_vars[(c, i)] = z3.Bool(f'in_{c}_{i}')
    
    solver = z3.Solver()
    
    # Constraint 1: Each day has exactly 1 or 2 cities
    for i in range(1, n_days + 1):
        day_vars = [in_vars[(c, i)] for c in cities]
        solver.add(z3.Or(z3.Sum([z3.If(v, 1, 0) for v in day_vars]) == 1, 
                   z3.Sum([z3.If(v, 1, 0) for v in day_vars]) == 2))
    
    # Constraint 2: Total days per city
    solver.add(z3.Sum([z3.If(in_vars[('P', i)], 1, 0) for i in range(1, n_days+1)]) == 4)
    solver.add(z3.Sum([z3.If(in_vars[('S', i)], 1, 0) for i in range(1, n_days+1)]) == 2)
    solver.add(z3.Sum([z3.If(in_vars[('Sp', i)], 1, 0) for i in range(1, n_days+1)]) == 2)
    solver.add(z3.Sum([z3.If(in_vars[('K', i)], 1, 0) for i in range(1, n_days+1)]) == 2)
    solver.add(z3.Sum([z3.If(in_vars[('F', i)], 1, 0) for i in range(1, n_days+1)]) == 2)
    
    # Constraint 3: Event constraints
    solver.add(in_vars[('S', 2)] == True)
    solver.add(in_vars[('S', 3)] == True)
    solver.add(in_vars[('Sp', 3)] == True)
    solver.add(in_vars[('Sp', 4)] == True)
    
    # Direct flights
    direct_flights = [('S','Sp'), ('P','F'), ('K','S'), ('K','Sp'), ('Sp','P'), ('K','P')]
    allowed_pairs = set(frozenset(pair) for pair in direct_flights)
    
    # Constraint 4: If two cities on same day, must have direct flight
    for i in range(1, n_days + 1):
        for c1 in cities:
            for c2 in cities:
                if c1 < c2 and frozenset([c1, c2]) not in allowed_pairs:
                    solver.add(z3.Not(z3.And(in_vars[(c1, i)], in_vars[(c2, i)])))
    
    # Constraint 5: Consecutive day city changes require flight on one of the days
    for i in range(1, n_days):
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    solver.add(
                        z3.Implies(
                            z3.And(in_vars[(c1, i)], in_vars[(c2, i+1)]),
                            z3.Or(
                                z3.And(in_vars[(c1, i)], in_vars[(c2, i)]),
                                z3.And(in_vars[(c1, i+1)], in_vars[(c2, i+1)])
                            )
                        )
                    )
    
    # Solve and output
    if solver.check() == z3.sat:
        model = solver.model()
        city_visits = {c: [] for c in cities}
        
        # Collect days for each city
        for c in cities:
            for i in range(1, n_days + 1):
                if z3.is_true(model.evaluate(in_vars[(c, i)])):
                    city_visits[c].append(i)
        
        # Create continuous intervals for each city
        itinerary_list = []
        for c in cities:
            days = sorted(city_visits[c])
            if not days:
                continue
            start = days[0]
            current = start
            for i in range(1, len(days)):
                if days[i] == current + 1:
                    current = days[i]
                else:
                    itinerary_list.append((start, current, c))
                    start = days[i]
                    current = days[i]
            itinerary_list.append((start, current, c))
        
        # Format itinerary
        itinerary_json = []
        for start, end, c in itinerary_list:
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary_json.append({"day_range": day_range, "place": city_names[c]})
        
        result = {"itinerary": itinerary_json}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()