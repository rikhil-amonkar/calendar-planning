from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Mykonos', 'Nice', 'Prague', 'Valencia', 'Zurich', 'Bucharest', 'Riga']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Mykonos': ['Nice', 'Zurich'],
        'Nice': ['Mykonos', 'Riga', 'Zurich'],
        'Prague': ['Bucharest', 'Riga', 'Valencia', 'Zurich'],
        'Valencia': ['Bucharest', 'Zurich', 'Prague'],
        'Zurich': ['Mykonos', 'Nice', 'Prague', 'Bucharest', 'Valencia', 'Riga'],
        'Bucharest': ['Prague', 'Valencia', 'Zurich', 'Riga'],
        'Riga': ['Nice', 'Bucharest', 'Prague', 'Zurich']
    }
    
    # Required days per city
    required_days = {
        'Valencia': 5,
        'Riga': 5,
        'Prague': 3,
        'Mykonos': 3,
        'Zurich': 5,
        'Bucharest': 5,
        'Nice': 2
    }
    
    total_days = 22
    
    # Create Z3 variables: day[i] is the city index for day i+1 (since days are 1-based)
    days = [Int(f'day_{i}') for i in range(total_days)]
    
    s = Solver()
    
    # Each day is assigned a city index (0 to 6)
    for day in days:
        s.add(And(day >= 0, day < len(cities)))
    
    # Constraint: Mykonos between day 1 and 3 (indices 0-2)
    s.add(Or([days[i] == city_map['Mykonos'] for i in range(3)]))
    
    # Constraint: Prague between day 7 and 9 (indices 6-8)
    s.add(Or([days[i] == city_map['Prague'] for i in range(6, 9)]))
    
    # Flight transitions: if day i and i+1 are different, there must be a direct flight
    for i in range(total_days - 1):
        current_city = days[i]
        next_city = days[i+1]
        # If current and next are different, check direct flight
        s.add(If(current_city != next_city,
                Or([And(current_city == city_map[c1], next_city == city_map[c2]) 
                    for c1 in direct_flights for c2 in direct_flights[c1]]),
                BoolVal(True)))
    
    # Contiguous stays: for each city, all its days must be in a single block
    for city in cities:
        city_idx = city_map[city]
        # days_in_city is a list of 1/0 indicating whether each day is in this city
        days_in_city = [If(days[i] == city_idx, 1, 0) for i in range(total_days)]
        # The sum must equal the required days
        s.add(Sum(days_in_city) == required_days[city])
        # To enforce contiguity: once we leave the city, we cannot come back
        # We can use a flag that, once set to False (indicating we've left the block), forbids any further 1's
        # This is a bit tricky in Z3, so we'll use an alternative approach
        # For any i < j < k, if days_in_city[i] and days_in_city[k] are 1, then days_in_city[j] must be 1
        for i in range(total_days):
            for k in range(i + 1, total_days):
                for j in range(i + 1, k):
                    s.add(If(And(days_in_city[i] == 1, days_in_city[k] == 1), days_in_city[j] == 1, BoolVal(True)))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city_idx = m.evaluate(days[0]).as_long()
        start_day = 1
        for i in range(1, total_days):
            city_idx = m.evaluate(days[i]).as_long()
            if city_idx != current_city_idx:
                itinerary.append({'day': f"{start_day}-{i}", 'place': cities[current_city_idx]})
                current_city_idx = city_idx
                start_day = i + 1
        itinerary.append({'day': f"{start_day}-{total_days}", 'place': cities[current_city_idx]})
        
        # Verify that the itinerary meets all constraints
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            start, end = map(int, entry['day'].split('-'))
            city_days[entry['place']] += end - start + 1
        for city in cities:
            assert city_days[city] == required_days[city], f"City {city} has {city_days[city]} days, expected {required_days[city]}"
        
        mykonos_days = []
        prague_days = []
        for i in range(total_days):
            city_idx = m.evaluate(days[i]).as_long()
            if cities[city_idx] == 'Mykonos':
                mykonos_days.append(i + 1)
            if cities[city_idx] == 'Prague':
                prague_days.append(i + 1)
        assert any(1 <= day <= 3 for day in mykonos_days), "Mykonos not visited in days 1-3"
        assert any(7 <= day <= 9 for day in prague_days), "Prague not visited in days 7-9"
        
        for i in range(total_days - 1):
            current_city_idx = m.evaluate(days[i]).as_long()
            next_city_idx = m.evaluate(days[i + 1]).as_long()
            if current_city_idx != next_city_idx:
                current_city = cities[current_city_idx]
                next_city = cities[next_city_idx]
                assert next_city in direct_flights[current_city], f"No direct flight from {current_city} to {next_city}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))