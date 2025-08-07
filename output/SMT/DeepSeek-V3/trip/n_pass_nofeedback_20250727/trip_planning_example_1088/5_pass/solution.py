import json
from z3 import *

def solve_itinerary():
    # Cities with their required stay durations
    cities = {
        'Oslo': 5,
        'Stuttgart': 5,
        'Reykjavik': 2,
        'Split': 3,
        'Geneva': 2,
        'Porto': 3,
        'Tallinn': 5,
        'Stockholm': 3
    }
    city_names = list(cities.keys())
    city_to_num = {city: idx for idx, city in enumerate(city_names)}
    num_to_city = {idx: city for idx, city in enumerate(city_names)}

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

    # Create flight connections graph
    flight_graph = {city: set() for city in city_names}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)

    # Create Z3 solver
    s = Solver()
    s.set("timeout", 30000)  # Give more time to find solution

    # Day variables (1-21)
    days = 21
    day_city = [Int(f'day_{i}') for i in range(1, days+1)]

    # Each day must be assigned a valid city
    for day in day_city:
        s.add(day >= 0, day < len(city_names))

    # Fixed constraints:
    # Days 1-2 in Reykjavik
    s.add(day_city[0] == city_to_num['Reykjavik'])
    s.add(day_city[1] == city_to_num['Reykjavik'])

    # Days 19-21 in Porto
    for i in range(18, 21):
        s.add(day_city[i] == city_to_num['Porto'])

    # Meet friend in Stockholm between days 2-4
    s.add(Or([day_city[i] == city_to_num['Stockholm'] for i in range(1, 4)]))

    # Flight transitions: consecutive days must be same city or connected
    for i in range(days-1):
        current = day_city[i]
        next_day = day_city[i+1]
        same_city = current == next_day
        connected = Or([And(current == city_to_num[a], next_day == city_to_num[b]) 
                       for a in flight_graph for b in flight_graph[a]])
        s.add(Or(same_city, connected))

    # Duration constraints
    for city, duration in cities.items():
        count = Sum([If(day_city[i] == city_to_num[city], 1, 0) for i in range(days)])
        s.add(count == duration)

    # Additional constraints to help guide the solver
    # Ensure we don't stay in one city for too long without moving
    for i in range(days-3):
        s.add(Or(day_city[i] != day_city[i+1], 
                day_city[i] != day_city[i+2],
                day_city[i] != day_city[i+3]))

    # Try to find solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_num = model.evaluate(day_city[i]).as_long()
            city = num_to_city[city_num]
            itinerary.append({"day": day_num, "place": city})
        
        # Verify the solution
        city_counts = {city: 0 for city in city_names}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        valid = all(city_counts[city] == cities[city] for city in cities)
        if valid:
            return {'itinerary': itinerary}
        else:
            return {"error": "Invalid solution found"}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))