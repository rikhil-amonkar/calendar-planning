from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as tuples of city indices
    direct_flights = [
        (city_map['Dubrovnik'], city_map['Stockholm']),
        (city_map['Lisbon'], city_map['Copenhagen']),
        (city_map['Lisbon'], city_map['Lyon']),
        (city_map['Copenhagen'], city_map['Stockholm']),
        (city_map['Copenhagen'], city_map['Split']),
        (city_map['Prague'], city_map['Stockholm']),
        (city_map['Tallinn'], city_map['Stockholm']),
        (city_map['Prague'], city_map['Lyon']),
        (city_map['Lisbon'], city_map['Stockholm']),
        (city_map['Prague'], city_map['Lisbon']),
        (city_map['Stockholm'], city_map['Split']),
        (city_map['Prague'], city_map['Copenhagen']),
        (city_map['Split'], city_map['Lyon']),
        (city_map['Copenhagen'], city_map['Dubrovnik']),
        (city_map['Prague'], city_map['Split']),
        (city_map['Tallinn'], city_map['Copenhagen']),
        (city_map['Tallinn'], city_map['Prague'])
    ]
    
    # Create a set of direct flight pairs for quick lookup
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Z3 solver
    solver = Solver()
    
    # Variables: day_1 to day_19, each is an integer representing city index
    days = [Int(f'day_{i}') for i in range(1, 20)]
    
    # Each day must be a valid city index (0 to 7)
    for day in days:
        solver.add(day >= 0, day < 8)
    
    # Flight transitions: if day_i and day_{i+1} are different, there must be a direct flight
    for i in range(len(days) - 1):
        day_current = days[i]
        day_next = days[i + 1]
        # If cities are different, ensure there's a direct flight
        solver.add(
            Implies(
                day_current != day_next,
                Or([And(day_current == a, day_next == b) for (a, b) in flight_pairs])
            )
        )
    
    # Duration constraints
    # Lisbon: 2 days (including flight days)
    lisbon_days = Sum([If(days[i] == city_map['Lisbon'], 1, 0) for i in range(19)])
    solver.add(lisbon_days == 2)
    
    # Workshop in Lisbon between day 4 and day 5 (i.e., day 4 or 5 is Lisbon)
    solver.add(Or(days[3] == city_map['Lisbon'], days[4] == city_map['Lisbon']))
    
    # Dubrovnik: 5 days
    dubrovnik_days = Sum([If(days[i] == city_map['Dubrovnik'], 1, 0) for i in range(19)])
    solver.add(dubrovnik_days == 5)
    
    # Copenhagen: 5 days
    copenhagen_days = Sum([If(days[i] == city_map['Copenhagen'], 1, 0) for i in range(19)])
    solver.add(copenhagen_days == 5)
    
    # Prague: 3 days
    prague_days = Sum([If(days[i] == city_map['Prague'], 1, 0) for i in range(19)])
    solver.add(prague_days == 3)
    
    # Tallinn: 2 days
    tallinn_days = Sum([If(days[i] == city_map['Tallinn'], 1, 0) for i in range(19)])
    solver.add(tallinn_days == 2)
    
    # Meet friend in Tallinn between day 1 and day 2 (i.e., day 0 or 1 is Tallinn)
    solver.add(Or(days[0] == city_map['Tallinn'], days[1] == city_map['Tallinn']))
    
    # Stockholm: 4 days
    stockholm_days = Sum([If(days[i] == city_map['Stockholm'], 1, 0) for i in range(19)])
    solver.add(stockholm_days == 4)
    
    # Wedding in Stockholm between day 13 and day 16 (i.e., days 12, 13, 14, or 15)
    solver.add(Or([days[i] == city_map['Stockholm'] for i in range(12, 16)]))
    
    # Split: 3 days
    split_days = Sum([If(days[i] == city_map['Split'], 1, 0) for i in range(19)])
    solver.add(split_days == 3)
    
    # Lyon: 2 days
    lyon_days = Sum([If(days[i] == city_map['Lyon'], 1, 0) for i in range(19)])
    solver.add(lyon_days == 2)
    
    # Annual show in Lyon from day 18 to day 19 (i.e., days 17 and 18)
    solver.add(days[17] == city_map['Lyon'])
    solver.add(days[18] == city_map['Lyon'])
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(19):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city_name = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city_name})
        
        # Verify the solution meets all constraints
        # (This step is implicit in the solver's sat check)
        
        # Output the itinerary as JSON
        import json
        output = {'itinerary': itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

solve_itinerary()