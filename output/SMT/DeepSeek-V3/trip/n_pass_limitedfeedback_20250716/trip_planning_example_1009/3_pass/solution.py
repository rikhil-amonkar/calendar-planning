from z3 import *
import json

def solve_itinerary():
    # Cities and their required durations
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
    
    # Create Z3 solver
    s = Solver()
    
    # Map cities to integers for Z3 variables
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Variables for each day (1..23)
    day_city = [Int(f'day_{i}') for i in range(1, 24)]
    
    # Each day must be a valid city
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: consecutive days must be the same city or connected by direct flight
    for i in range(22):  # days 1..22, next is i+1 (2..23)
        current_day = day_city[i]
        next_day = day_city[i+1]
        same_city = current_day == next_day
        flight_possible = Or([And(current_day == city_to_int[a], next_day == city_to_int[b]) 
                             for a in direct_flights for b in direct_flights[a]])
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