from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = {
        'Brussels': 0,
        'Helsinki': 1,
        'Split': 2,
        'Dubrovnik': 3,
        'Istanbul': 4,
        'Milan': 5,
        'Vilnius': 6,
        'Frankfurt': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 4, 5, 6, 7],  # Brussels
        1: [0, 3, 4, 5, 6, 7, 2],  # Helsinki
        2: [1, 5, 6, 7],  # Split
        3: [1, 4, 7],  # Dubrovnik
        4: [0, 1, 5, 6, 7],  # Istanbul
        5: [0, 1, 2, 6, 7],  # Milan
        6: [0, 1, 2, 4, 5, 7],  # Vilnius
        7: [0, 1, 2, 3, 4, 5, 6]  # Frankfurt
    }
    
    # Required days per city
    required_days = {
        'Brussels': 3,
        'Helsinki': 3,
        'Split': 4,
        'Dubrovnik': 2,
        'Istanbul': 5,
        'Milan': 4,
        'Vilnius': 5,
        'Frankfurt': 3
    }
    
    # Fixed events
    fixed_events = [
        (1, 5, 'Istanbul'),  # Days 1-5 in Istanbul
        (16, 18, 'Frankfurt'),  # Days 16-18 in Frankfurt
        (18, 22, 'Vilnius')   # Days 18-22 in Vilnius
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city on day i+1 (days 1..22)
    days = [Int(f'day_{i}') for i in range(22)]
    for day in days:
        s.add(day >= 0, day <= 7)
    
    # Fixed events constraints
    for (start, end, city) in fixed_events:
        city_idx = cities[city]
        for day in range(start - 1, end):
            s.add(days[day] == city_idx)
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(21):
        current_city = days[i]
        next_city = days[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            And(current_city != next_city, next_city in direct_flights[current_city])
        ))
    
    # Duration constraints: count days per city
    for city, idx in cities.items():
        required = required_days[city]
        # Count occurrences of city in days
        count = Sum([If(days[i] == idx, 1, 0) for i in range(22)])
        s.add(count == required)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(22):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({
                'day': i + 1,
                'city': city_names[city_idx]
            })
        
        # Verify transitions
        for i in range(21):
            current_city = itinerary[i]['city']
            next_city = itinerary[i + 1]['city']
            if current_city != next_city:
                current_idx = cities[current_city]
                next_idx = cities[next_city]
                assert next_idx in direct_flights[current_idx], \
                    f"No direct flight from {current_city} to {next_city} between day {i+1} and {i+2}"
        
        # Verify durations
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['city']] += 1
        for city, req in required_days.items():
            assert city_counts[city] == req, f"{city} days mismatch: {city_counts[city]} vs {req}"
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")