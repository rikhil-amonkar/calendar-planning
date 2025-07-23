from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Riga', 'Manchester', 'Bucharest', 'Florence', 'Vienna', 'Istanbul', 'Reykjavik', 'Stuttgart']
    city_durations = {
        'Riga': 4,
        'Manchester': 5,
        'Bucharest': 4,
        'Florence': 4,
        'Vienna': 2,
        'Istanbul': 2,
        'Reykjavik': 4,
        'Stuttgart': 5
    }
    
    # Direct flights as adjacency list
    direct_flights = {
        'Bucharest': ['Vienna', 'Riga', 'Istanbul', 'Manchester'],
        'Vienna': ['Bucharest', 'Reykjavik', 'Manchester', 'Riga', 'Istanbul', 'Florence', 'Stuttgart'],
        'Reykjavik': ['Vienna', 'Stuttgart'],
        'Manchester': ['Vienna', 'Riga', 'Istanbul', 'Bucharest', 'Stuttgart'],
        'Riga': ['Manchester', 'Vienna', 'Bucharest', 'Istanbul'],
        'Istanbul': ['Vienna', 'Riga', 'Stuttgart', 'Bucharest', 'Manchester'],
        'Florence': ['Vienna'],
        'Stuttgart': ['Vienna', 'Istanbul', 'Reykjavik', 'Manchester']
    }
    
    # Fixed events
    # Bucharest workshop between day 16 and 19 (inclusive)
    # Istanbul show on day 12 and 13
    
    # Create Z3 variables for each day (1..23)
    s = Solver()
    day_city = [Int(f'day_{i}_city') for i in range(1, 24)]  # days 1..23
    
    # Map cities to integers
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints: each day_city must be between 0 and 7 (inclusive)
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: consecutive days must be the same city or connected by direct flight
    for i in range(22):  # days 1..22, next is i+1 (2..23)
        current_day = day_city[i]
        next_day = day_city[i+1]
        # Either same city or direct flight exists
        same_city = current_day == next_day
        flight_possible = Or([And(current_day == city_to_int[a], next_day == city_to_int[b]) 
                             for a in direct_flights 
                             for b in direct_flights[a] if a in city_to_int and b in city_to_int])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints: count occurrences of each city in day_city
    for city in cities:
        duration = city_durations[city]
        s.add(Sum([If(day == city_to_int[city], 1, 0) for day in day_city]) == duration)
    
    # Fixed events:
    # Istanbul on days 12 and 13 (indices 11 and 12 in 0-based)
    s.add(day_city[11] == city_to_int['Istanbul'])  # day 12
    s.add(day_city[12] == city_to_int['Istanbul'])  # day 13
    
    # Bucharest between day 16 and 19 (indices 15..18 in 0-based)
    # At least one of these days is Bucharest
    s.add(Or([day_city[i] == city_to_int['Bucharest'] for i in range(15, 19)]))  # days 16-19
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(23):
            day_num = i + 1
            city_idx = model.evaluate(day_city[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day_num, 'city': city})
        
        # Verify durations
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['city']] += 1
        for city in cities:
            assert city_counts[city] == city_durations[city], f"Duration mismatch for {city}"
        
        # Verify flights
        for i in range(22):
            current_city = itinerary[i]['city']
            next_city = itinerary[i+1]['city']
            if current_city != next_city:
                assert next_city in direct_flights[current_city], f"No direct flight from {current_city} to {next_city} on day {i+1}"
        
        # Verify fixed events
        istanbul_days = [entry['day'] for entry in itinerary if entry['city'] == 'Istanbul']
        assert 12 in istanbul_days and 13 in istanbul_days, "Istanbul show days not satisfied"
        
        bucharest_days = [entry['day'] for entry in itinerary if entry['city'] == 'Bucharest']
        has_workshop = any(16 <= day <= 19 for day in bucharest_days)
        assert has_workshop, "Bucharest workshop not between days 16-19"
        
        # Prepare JSON output
        output = {'itinerary': itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))