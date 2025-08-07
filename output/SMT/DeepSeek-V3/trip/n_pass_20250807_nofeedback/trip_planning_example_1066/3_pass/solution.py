from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 'Helsinki', 'Split', 'London']
    
    # Direct flights as per the problem description
    direct_flights = {
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Mykonos', 'Bucharest', 'Brussels'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Split', 'Mykonos', 'Stuttgart'],
        'Brussels': ['London', 'Bucharest', 'Madrid', 'Helsinki'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Stuttgart': ['London', 'Split'],
        'Mykonos': ['Madrid', 'London']
    }
    
    # Create a mapping from city names to integers
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Days: 1 to 21
    days = 21
    
    # Create Z3 variables for each day: which city are you in?
    day_city = [Int(f'day_{i+1}_city') for i in range(days)]
    
    s = Solver()
    
    # Each day_city variable must be between 0 and 7 (inclusive)
    for dc in day_city:
        s.add(dc >= 0, dc < len(cities))
    
    # Constraint: consecutive days must be same city or have a direct flight
    for i in range(days - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        # Either stay in the same city or fly to a directly connected city
        s.add(Or(
            current == next_c,
            Or([And(current == city_to_int[c], next_c == city_to_int[n]) 
                for c in direct_flights for n in direct_flights[c]])
        ))
    
    # Duration constraints
    # Brussels: 4 days
    s.add(Sum([If(day_city[i] == city_to_int['Brussels'], 1, 0) for i in range(days)]) == 4)
    
    # Bucharest: 3 days
    s.add(Sum([If(day_city[i] == city_to_int['Bucharest'], 1, 0) for i in range(days)]) == 3)
    
    # Stuttgart: 4 days
    s.add(Sum([If(day_city[i] == city_to_int['Stuttgart'], 1, 0) for i in range(days)]) == 4)
    
    # Mykonos: 2 days
    s.add(Sum([If(day_city[i] == city_to_int['Mykonos'], 1, 0) for i in range(days)]) == 2)
    
    # Madrid: 2 days (conference on days 20 and 21)
    s.add(Sum([If(day_city[i] == city_to_int['Madrid'], 1, 0) for i in range(days)]) == 2)
    s.add(day_city[19] == city_to_int['Madrid'])  # day 20 is index 19 (0-based)
    s.add(day_city[20] == city_to_int['Madrid'])  # day 21 is index 20
    
    # Helsinki: 5 days
    s.add(Sum([If(day_city[i] == city_to_int['Helsinki'], 1, 0) for i in range(days)]) == 5)
    
    # Split: 3 days
    s.add(Sum([If(day_city[i] == city_to_int['Split'], 1, 0) for i in range(days)]) == 3)
    
    # London: 5 days
    s.add(Sum([If(day_city[i] == city_to_int['London'], 1, 0) for i in range(days)]) == 5)
    
    # Stuttgart visit between day 1 and day 4 (i.e., at least one day in 0..3 is Stuttgart)
    s.add(Or([day_city[i] == city_to_int['Stuttgart'] for i in range(4)]))  # days 1-4 (0-based 0-3)
    
    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day_city[i]).as_long()
            city_name = int_to_city[city_idx]
            itinerary.append({'day': i+1, 'place': city_name})
        
        # Verify the durations
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Print for verification
        print("Day counts per city:")
        for city, cnt in counts.items():
            print(f"{city}: {cnt} days")
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))