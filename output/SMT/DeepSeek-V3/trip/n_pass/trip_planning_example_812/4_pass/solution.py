import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    
    # Direct flights as a dictionary for quick lookup
    direct_flights = {
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Paris': ['Warsaw', 'Florence', 'Vienna', 'Porto', 'Nice', 'Munich'],
        'Munich': ['Vienna', 'Florence', 'Warsaw', 'Nice', 'Porto', 'Paris'],
        'Porto': ['Vienna', 'Munich', 'Nice', 'Paris', 'Warsaw'],
        'Warsaw': ['Paris', 'Vienna', 'Munich', 'Nice', 'Porto'],
        'Nice': ['Vienna', 'Munich', 'Warsaw', 'Porto', 'Paris']
    }
    
    # Create a reverse mapping for flights (undirected, so already covered)
    
    # Day variables: each day is assigned a city
    day_to_city = [Int(f'day_{i}_city') for i in range(1, 21)]
    
    # City encodings (assign each city a unique integer)
    city_ids = {
        'Paris': 0,
        'Florence': 1,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 4,
        'Nice': 5,
        'Warsaw': 6
    }
    id_to_city = {v: k for k, v in city_ids.items()}
    
    s = Solver()
    
    # Each day must be one of the cities
    for day_var in day_to_city:
        s.add(Or([day_var == city_ids[city] for city in cities]))
    
    # Flight transitions: consecutive days must be same city or have a direct flight
    for i in range(19):
        current_day = day_to_city[i]
        next_day = day_to_city[i + 1]
        # Either stay in the same city or move to a connected city
        same_city = current_day == next_day
        possible_flights = []
        for city, cid in city_ids.items():
            for target_city, tid in city_ids.items():
                if city != target_city and target_city in direct_flights[city]:
                    possible_flights.append(And(current_day == cid, next_day == tid))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Constraint: Porto between day 1-3 (days 1, 2, 3 are Porto)
    s.add(day_to_city[0] == city_ids['Porto'])
    s.add(day_to_city[1] == city_ids['Porto'])
    s.add(day_to_city[2] == city_ids['Porto'])
    
    # Warsaw between day 13-15 (days 13, 14, 15 are 1-based, so indices 12, 13, 14)
    s.add(day_to_city[12] == city_ids['Warsaw'])
    s.add(day_to_city[13] == city_ids['Warsaw'])
    s.add(day_to_city[14] == city_ids['Warsaw'])
    
    # Vienna between day 19-20 (indices 18 and 19)
    s.add(day_to_city[18] == city_ids['Vienna'])
    s.add(day_to_city[19] == city_ids['Vienna'])
    
    # Count the days per city (including overlaps)
    # For each city, the count is the number of days assigned to it.
    city_day_counts = []
    for city, cid in city_ids.items():
        count = Sum([If(day_var == cid, 1, 0) for day_var in day_to_city])
        city_day_counts.append((city, count))
    
    # Add constraints for each city's required days
    for city, required_days in cities.items():
        cid = city_ids[city]
        total = Sum([If(day_var == cid, 1, 0) for day_var in day_to_city])
        s.add(total == required_days)
    
    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            day = i + 1
            city_id = model.evaluate(day_to_city[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': day, 'city': city})
        
        # Verify day counts
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            day_counts[entry['city']] += 1
        
        for city, required in cities.items():
            assert day_counts[city] == required, f"City {city} has {day_counts[city]} days, expected {required}"
        
        # Verify transitions
        for i in range(19):
            current_city = itinerary[i]['city']
            next_city = itinerary[i+1]['city']
            if current_city != next_city:
                assert next_city in direct_flights[current_city], f"No flight from {current_city} to {next_city}"
        
        # Prepare the output
        output = {
            'itinerary': itinerary
        }
        return output
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")