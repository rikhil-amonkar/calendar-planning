from z3 import *

def solve_scheduling():
    # Cities with correct spellings
    cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Corrected direct flights adjacency list
    direct_flights = {
        'Prague': ['Tallinn', 'Zurich', 'Florence', 'Bucharest', 'Frankfurt'],
        'Tallinn': ['Prague', 'Frankfurt', 'Zurich'],
        'Zurich': ['Prague', 'Florence', 'Bucharest', 'Frankfurt', 'Venice'],
        'Florence': ['Prague', 'Frankfurt', 'Zurich'],
        'Frankfurt': ['Bucharest', 'Venice', 'Tallinn', 'Zurich', 'Prague', 'Florence'],
        'Bucharest': ['Frankfurt', 'Prague', 'Zurich'],
        'Venice': ['Frankfurt', 'Zurich']
    }
    
    # Create solver with optimized strategy
    s = Solver()
    s.set("timeout", 60000)  # 60 second timeout
    
    # Day variables (1-26)
    days = [Int(f"day_{i}") for i in range(1, 27)]
    
    # Each day must be a valid city
    for day in days:
        s.add(day >= 0, day <= 6)
    
    # Transition constraints
    for i in range(25):
        current = days[i]
        next_day = days[i+1]
        # Either stay or take a direct flight
        s.add(Or(
            current == next_day,
            Or([And(current == city_to_idx[a], next_day == city_to_idx[b]) 
               for a in direct_flights for b in direct_flights[a]])
        ))
    
    # City stay durations
    s.add(Sum([If(d == city_to_idx['Bucharest'], 1, 0) for d in days]) == 3)
    s.add(Sum([If(d == city_to_idx['Venice'], 1, 0) for d in days]) == 5)
    s.add(Sum([If(d == city_to_idx['Prague'], 1, 0) for d in days]) == 4)
    s.add(Sum([If(d == city_to_idx['Frankfurt'], 1, 0) for d in days]) == 5)
    s.add(Sum([If(d == city_to_idx['Zurich'], 1, 0) for d in days]) == 5)
    s.add(Sum([If(d == city_to_idx['Florence'], 1, 0) for d in days]) == 5)
    s.add(Sum([If(d == city_to_idx['Tallinn'], 1, 0) for d in days]) == 5)
    
    # Event constraints
    # Wedding in Venice between days 22-26
    s.add(Or([days[i] == city_to_idx['Venice'] for i in range(21, 26)]))
    # Frankfurt show days 12-16
    for i in range(11, 16):
        s.add(days[i] == city_to_idx['Frankfurt'])
    # Tallinn friends days 8-12
    s.add(Or([days[i] == city_to_idx['Tallinn'] for i in range(7, 12)]))
    
    # Additional constraints to help solver
    # Must start somewhere (day 1)
    s.add(Or([days[0] == i for i in range(7)]))
    # Must end somewhere (day 26)
    s.add(Or([days[25] == i for i in range(7)]))
    
    # Try to find solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(26):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({"day": day_num, "place": city})
        
        # Verify all constraints are met
        # (Additional verification could be added here)
        
        # Format output
        import json
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No valid itinerary found after optimization.")

solve_scheduling()