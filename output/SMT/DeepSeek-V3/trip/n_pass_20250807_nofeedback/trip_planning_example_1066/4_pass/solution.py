from z3 import *

def solve_itinerary():
    # Cities with their required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,  # Conference on days 20-21
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Direct flight connections (bidirectional)
    flight_connections = [
        ('Helsinki', 'London'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Brussels'),
        ('Helsinki', 'Split'),
        ('Split', 'Madrid'),
        ('Split', 'London'),
        ('Split', 'Stuttgart'),
        ('Madrid', 'London'),
        ('Madrid', 'Mykonos'),
        ('Madrid', 'Bucharest'),
        ('Madrid', 'Brussels'),
        ('London', 'Brussels'),
        ('London', 'Bucharest'),
        ('London', 'Mykonos'),
        ('London', 'Stuttgart'),
        ('Brussels', 'Bucharest'),
        ('Brussels', 'Madrid'),
        ('Bucharest', 'Madrid'),
        ('Stuttgart', 'London'),
        ('Mykonos', 'Madrid')
    ]

    # Create mappings between city names and integers
    city_list = list(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    int_to_city = {idx: city for idx, city in enumerate(city_list)}

    # Days in the itinerary
    total_days = 21
    
    # Create Z3 variables for each day's city
    day_city = [Int(f'day_{i+1}') for i in range(total_days)]
    
    s = Solver()

    # Each day must be assigned a valid city
    for dc in day_city:
        s.add(dc >= 0, dc < len(city_list))

    # Flight constraints between consecutive days
    for i in range(total_days - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        # Either stay in same city or have a direct flight
        s.add(Or(
            current == next_c,
            Or([And(current == city_to_int[c1], next_c == city_to_int[c2]) 
               for (c1, c2) in flight_connections] + 
               [And(current == city_to_int[c2], next_c == city_to_int[c1]) 
               for (c1, c2) in flight_connections])
        ))

    # Duration constraints for each city
    for city, days_needed in cities.items():
        s.add(Sum([If(day_city[i] == city_to_int[city], 1, 0) 
              for i in range(total_days)]) == days_needed)

    # Special constraints
    # Conference in Madrid on days 20-21 (indices 19-20)
    s.add(day_city[19] == city_to_int['Madrid'])
    s.add(day_city[20] == city_to_int['Madrid'])
    
    # Visit Stuttgart between days 1-4 (indices 0-3)
    s.add(Or([day_city[i] == city_to_int['Stuttgart'] for i in range(4)]))

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(total_days):
            city_idx = model.evaluate(day_city[i]).as_long()
            city_name = int_to_city[city_idx]
            itinerary.append({'day': i+1, 'place': city_name})
        
        # Verify the solution
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        print("Verification:")
        for city, cnt in counts.items():
            print(f"{city}: {cnt} days (required: {cities[city]})")
        
        return {'itinerary': itinerary}
    else:
        print("Failed to find a valid itinerary")
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))