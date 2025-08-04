import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Oslo', 'Stuttgart', 'Reykjavik', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Reykjavik', 'Stuttgart'),
        ('Reykjavik', 'Stockholm'),
        ('Reykjavik', 'Tallinn'),
        ('Stockholm', 'Oslo'),
        ('Stuttgart', 'Porto'),
        ('Oslo', 'Split'),
        ('Stockholm', 'Stuttgart'),
        ('Reykjavik', 'Oslo'),
        ('Oslo', 'Geneva'),
        ('Stockholm', 'Split'),
        ('Reykjavik', 'Stockholm'),
        ('Split', 'Stuttgart'),
        ('Tallinn', 'Oslo'),
        ('Stockholm', 'Geneva'),
        ('Oslo', 'Porto'),
        ('Geneva', 'Porto'),
        ('Geneva', 'Split')
    ]
    
    # Create a flight adjacency list
    flight_graph = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Required days per city
    required_days = {
        'Oslo': 5,
        'Stuttgart': 5,
        'Reykjavik': 2,
        'Split': 3,
        'Geneva': 2,
        'Porto': 3,
        'Tallinn': 5,
        'Stockholm': 3
    }
    
    # Fixed events
    fixed_events = {
        1: 'Reykjavik',
        2: 'Reykjavik',
        19: 'Porto',
        20: 'Porto',
        21: 'Porto'
    }
    
    # Meeting in Stockholm between day 2 and day 4 (i.e., days 3 or 4)
    # So Stockholm must be visited on at least one of these days
    
    # Create Z3 variables: itinerary[day] = city index
    itinerary = [Int(f'day_{day}') for day in range(1, 22)]
    
    s = Solver()
    
    # Each day's assignment must be a valid city index (0 to 7)
    for day in range(1, 22):
        s.add(And(itinerary[day - 1] >= 0, itinerary[day - 1] < 8))
    
    # Fixed events
    for day, city in fixed_events.items():
        s.add(itinerary[day - 1] == city_map[city])
    
    # Stockholm must be visited between day 2 and day 4 (days 3 or 4)
    s.add(Or(
        itinerary[2] == city_map['Stockholm'],  # day 3
        itinerary[3] == city_map['Stockholm']   # day 4
    ))
    
    # Flight constraints: consecutive days must be the same city or connected by a direct flight
    for day in range(1, 21):
        current_city_idx = itinerary[day - 1]
        next_city_idx = itinerary[day]
        current_city = cities[current_city_idx]
        next_city = cities[next_city_idx]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city_idx == next_city_idx,
            And(current_city_idx != next_city_idx, next_city in flight_graph[current_city])
        ))
    
    # Count the number of days spent in each city
    city_days = {}
    for city in cities:
        city_idx = city_map[city]
        # Sum over all days where itinerary[day] == city_idx
        city_days[city] = Sum([If(itinerary[day] == city_idx, 1, 0) for day in range(21)])
    
    # Add constraints for required days per city
    for city, days in required_days.items():
        s.add(city_days[city] == days)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the itinerary
        itinerary_result = []
        for day in range(1, 22):
            city_idx = model.evaluate(itinerary[day - 1]).as_long()
            itinerary_result.append({'day': day, 'place': cities[city_idx]})
        
        # Verify the counts
        city_counts = {city: 0 for city in cities}
        for entry in itinerary_result:
            city_counts[entry['place']] += 1
        for city, req in required_days.items():
            assert city_counts[city] == req, f"City {city} has {city_counts[city]} days, expected {req}"
        
        # Verify flights
        for day in range(1, 21):
            current_place = itinerary_result[day - 1]['place']
            next_place = itinerary_result[day]['place']
            if current_place != next_place:
                assert next_place in flight_graph[current_place], f"No flight from {current_place} to {next_place} on day {day}"
        
        # Verify fixed events
        for day, city in fixed_events.items():
            assert itinerary_result[day - 1]['place'] == city, f"Day {day} should be in {city}"
        
        # Verify Stockholm meeting
        stockholm_days = [entry['day'] for entry in itinerary_result if entry['place'] == 'Stockholm']
        assert any(2 < day <=4 for day in stockholm_days), "Stockholm not visited between day 2 and 4"
        
        return {'itinerary': itinerary_result}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")