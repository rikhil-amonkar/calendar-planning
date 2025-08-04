import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    
    # Direct flights as adjacency list
    direct_flights = {
        'Reykjavik': ['Munich', 'Oslo', 'Frankfurt', 'Barcelona', 'Stockholm'],
        'Munich': ['Reykjavik', 'Frankfurt', 'Bucharest', 'Stockholm', 'Oslo', 'Split', 'Barcelona'],
        'Frankfurt': ['Munich', 'Oslo', 'Bucharest', 'Barcelona', 'Reykjavik', 'Stockholm', 'Split'],
        'Oslo': ['Split', 'Reykjavik', 'Frankfurt', 'Bucharest', 'Barcelona', 'Stockholm', 'Munich'],
        'Bucharest': ['Munich', 'Barcelona', 'Oslo', 'Frankfurt'],
        'Barcelona': ['Bucharest', 'Frankfurt', 'Reykjavik', 'Stockholm', 'Split', 'Oslo', 'Munich'],
        'Stockholm': ['Barcelona', 'Reykjavik', 'Munich', 'Oslo', 'Split', 'Frankfurt'],
        'Split': ['Oslo', 'Barcelona', 'Stockholm', 'Frankfurt', 'Munich']
    }
    
    # Total days
    total_days = 20
    
    # Create Z3 variables: day[i] is the city on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(total_days)]
    
    # City to integer mapping
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Solver
    s = Solver()
    
    # Each day must be a valid city (0 to 7)
    for d in day:
        s.add(And(d >= 0, d < len(cities)))
    
    # Constraints for days in each city
    counts = {city: Sum([If(day[i] == city_to_int[city], 1, 0) for i in range(total_days)]) for city in cities}
    
    s.add(counts['Oslo'] == 2)
    s.add(counts['Reykjavik'] == 5)
    s.add(counts['Stockholm'] == 4)
    s.add(counts['Munich'] == 4)
    s.add(counts['Frankfurt'] == 4)
    s.add(counts['Barcelona'] == 3)
    s.add(counts['Bucharest'] == 2)
    s.add(counts['Split'] == 3)
    
    # Fixed constraints:
    # Oslo on days 16 and 17 (0-based days 15 and 16)
    s.add(day[15] == city_to_int['Oslo'])
    s.add(day[16] == city_to_int['Oslo'])
    
    # Reykjavik: at least one day between 9-13 (0-based days 8 to 12)
    s.add(Or([day[i] == city_to_int['Reykjavik'] for i in range(8, 13)]))
    
    # Munich between days 13-16 (0-based 12 to 15)
    s.add(Or([day[i] == city_to_int['Munich'] for i in range(12, 16)]))
    
    # Frankfurt between days 17-20 (0-based 16 to 19)
    s.add(Or([day[i] == city_to_int['Frankfurt'] for i in range(16, 20)]))
    
    # Flight constraints: consecutive days can only be same city or connected by direct flight
    for i in range(total_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        same_city = current_city == next_city
        flight_possible = Or([And(current_city == city_to_int[a], next_city == city_to_int[b]) 
                            for a in direct_flights for b in direct_flights[a]])
        s.add(Or(same_city, flight_possible))
    
    # Set a timeout for the solver (in milliseconds)
    s.set("timeout", 60000)  # 60 seconds
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(total_days):
            city_idx = m.evaluate(day[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": i+1, "place": city})
        
        # Verify counts
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        # Verify specific constraints
        assert city_counts['Oslo'] == 2
        assert city_counts['Reykjavik'] == 5
        assert city_counts['Stockholm'] == 4
        assert city_counts['Munich'] == 4
        assert city_counts['Frankfurt'] == 4
        assert city_counts['Barcelona'] == 3
        assert city_counts['Bucharest'] == 2
        assert city_counts['Split'] == 3
        
        # Check Oslo on days 16-17
        assert itinerary[15]['place'] == 'Oslo'
        assert itinerary[16]['place'] == 'Oslo'
        
        # Reykjavik between days 9-13
        reyk_days = [entry['day'] for entry in itinerary if entry['place'] == 'Reykjavik']
        assert any(9 <= day <= 13 for day in reyk_days)
        
        # Munich between 13-16
        munich_days = [entry['day'] for entry in itinerary if entry['place'] == 'Munich']
        assert any(13 <= day <= 16 for day in munich_days)
        
        # Frankfurt between 17-20
        frankfurt_days = [entry['day'] for entry in itinerary if entry['place'] == 'Frankfurt']
        assert any(17 <= day <= 20 for day in frankfurt_days)
        
        # Verify flight connections
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                assert next_place in direct_flights[current], f"No flight from {current} to {next_place} on day {i+1}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found within the time limit"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))