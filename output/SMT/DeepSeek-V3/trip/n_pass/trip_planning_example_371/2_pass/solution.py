from z3 import *

def solve_itinerary():
    # Cities encoding
    cities = {'Nice': 0, 'Stockholm': 1, 'Split': 2, 'Vienna': 3}
    city_names = {0: 'Nice', 1: 'Stockholm', 2: 'Split', 3: 'Vienna'}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3],  # Nice: Stockholm, Vienna
        1: [0, 2, 3],  # Stockholm: Nice, Split, Vienna
        2: [1, 3],  # Split: Stockholm, Vienna
        3: [0, 1, 2]  # Vienna: Nice, Stockholm, Split
    }
    
    # Create Z3 variables for each day (1-based)
    days = [Int(f'day_{i}') for i in range(1, 10)]  # days 1 to 9
    
    solver = Solver()
    
    # Constraint: each day's city must be 0, 1, 2, or 3
    for day in days:
        solver.add(Or([day == c for c in cities.values()]))
    
    # Constraint: transitions between cities must be direct flights
    for i in range(len(days) - 1):
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        solver.add(Or(
            current_day == next_day,
            *[And(current_day == u, next_day == v) 
              for u in direct_flights.keys() 
              for v in direct_flights[u]]
        ))
    
    # Days in each city constraints
    nice_days = Sum([If(days[i] == cities['Nice'], 1, 0) for i in range(9)])
    stockholm_days = Sum([If(days[i] == cities['Stockholm'], 1, 0) for i in range(9)])
    split_days = Sum([If(days[i] == cities['Split'], 1, 0) for i in range(9)])
    vienna_days = Sum([If(days[i] == cities['Vienna'], 1, 0) for i in range(9)])
    
    solver.add(nice_days == 2)
    solver.add(stockholm_days == 5)
    solver.add(split_days == 3)
    solver.add(vienna_days == 2)
    
    # Fixed events:
    # Conference in Split on day 7 and day 9 (1-based, so days[6] and days[8])
    solver.add(days[6] == cities['Split'])  # day 7
    solver.add(days[8] == cities['Split'])  # day 9
    
    # Workshop in Vienna between day 1 and day 2: at least one of day 1 or day 2 must be Vienna
    solver.add(Or(days[0] == cities['Vienna'], days[1] == cities['Vienna']))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(9):
            day_num = i + 1
            city_code = model.evaluate(days[i]).as_long()
            city_name = city_names[city_code]
            itinerary.append({'day': day_num, 'place': city_name})
        
        # Verify the solution meets all constraints
        # (Z3 should ensure this, but double-checking for sanity)
        # Convert itinerary to a dictionary for easier processing
        itinerary_dict = {day['day']: day['place'] for day in itinerary}
        
        # Check transitions
        valid = True
        for i in range(1, 9):
            prev_city = itinerary_dict[i]
            current_city = itinerary_dict[i+1]
            if prev_city != current_city:
                u = cities[prev_city]
                v = cities[current_city]
                if v not in direct_flights[u]:
                    valid = False
                    break
        
        if not valid:
            print("Invalid transitions found in the solution.")
            return None
        
        # Check day counts
        city_counts = {
            'Nice': 0,
            'Stockholm': 0,
            'Split': 0,
            'Vienna': 0
        }
        for day in itinerary:
            city_counts[day['place']] += 1
        
        expected_counts = {
            'Nice': 2,
            'Stockholm': 5,
            'Split': 3,
            'Vienna': 2
        }
        
        if city_counts != expected_counts:
            print("Day counts do not match expected values.")
            return None
        
        # Check fixed events
        if itinerary_dict[7] != 'Split' or itinerary_dict[9] != 'Split':
            print("Conference days are incorrect.")
            return None
        
        # Check workshop in Vienna between day 1 and day 2
        if itinerary_dict[1] != 'Vienna' and itinerary_dict[2] != 'Vienna':
            print("Workshop constraint not met.")
            return None
        
        return {'itinerary': itinerary}
    else:
        print("No solution found.")
        return None

# Execute the solver
result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))