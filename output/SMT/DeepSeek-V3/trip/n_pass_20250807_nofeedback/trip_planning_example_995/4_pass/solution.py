import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Oslo': 2,
        'Stuttgart': 3,
        'Venice': 4,
        'Split': 4,
        'Barcelona': 3,
        'Brussels': 3,
        'Copenhagen': 3
    }
    city_list = list(cities.keys())
    city_ids = {city: idx for idx, city in enumerate(city_list)}
    id_to_city = {v: k for k, v in city_ids.items()}

    # Direct flights (bidirectional)
    direct_flights = [
        ('Venice', 'Stuttgart'),
        ('Venice', 'Barcelona'),
        ('Venice', 'Brussels'),
        ('Venice', 'Oslo'),
        ('Venice', 'Copenhagen'),
        ('Stuttgart', 'Barcelona'),
        ('Stuttgart', 'Copenhagen'),
        ('Stuttgart', 'Split'),
        ('Oslo', 'Brussels'),
        ('Oslo', 'Split'),
        ('Oslo', 'Venice'),
        ('Oslo', 'Copenhagen'),
        ('Oslo', 'Barcelona'),
        ('Split', 'Copenhagen'),
        ('Split', 'Barcelona'),
        ('Split', 'Stuttgart'),
        ('Barcelona', 'Copenhagen'),
        ('Barcelona', 'Brussels'),
        ('Barcelona', 'Oslo'),
        ('Brussels', 'Copenhagen'),
        ('Brussels', 'Barcelona'),
        ('Copenhagen', 'Stuttgart'),
        ('Copenhagen', 'Venice')
    ]

    # Create flight adjacency list
    flight_graph = {city: set() for city in city_list}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)

    s = Solver()
    days = 16
    day_to_city = [Int(f'day_{i}') for i in range(days)]

    # Each day must be a valid city
    for day in day_to_city:
        s.add(day >= 0, day < len(city_list))

    # Duration constraints
    for city, duration in cities.items():
        s.add(Sum([If(day_to_city[i] == city_ids[city], 1, 0) for i in range(days)]) == duration)

    # Barcelona from day 1 to day 3 (1-based days 1-3, 0-based 0-2)
    for i in range(3):
        s.add(day_to_city[i] == city_ids['Barcelona'])

    # Oslo between day 3 and 4 (must include day 4)
    s.add(Or(
        day_to_city[3] == city_ids['Oslo'],
        day_to_city[4] == city_ids['Oslo']
    ))

    # Brussels between day 9 and 11 (1-based days 9-11, 0-based 8-10)
    s.add(Or(
        day_to_city[8] == city_ids['Brussels'],
        day_to_city[9] == city_ids['Brussels'],
        day_to_city[10] == city_ids['Brussels']
    ))

    # Flight constraints
    for i in range(days - 1):
        current = day_to_city[i]
        next_day = day_to_city[i + 1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current == next_day,
            *[And(current == city_ids[a], next_day == city_ids[b])
              for a in flight_graph for b in flight_graph[a]
            ]
        ))

    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_id = model.evaluate(day_to_city[i]).as_long()
            itinerary.append({'day': i + 1, 'place': id_to_city[city_id]})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in city_list}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city, req in cities.items():
            assert city_days[city] == req, f"{city} has {city_days[city]} days instead of {req}"
        
        # Verify Barcelona days 1-3
        assert all(itinerary[i]['place'] == 'Barcelona' for i in range(3))
        
        # Verify Oslo between days 4-5
        assert any(itinerary[i]['place'] == 'Oslo' for i in [3,4])
        
        # Verify Brussels between days 9-11
        assert any(itinerary[i]['place'] == 'Brussels' for i in [8,9,10])
        
        # Verify flights
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current != next_city:
                assert next_city in flight_graph[current], f"No flight from {current} to {next_city}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print
print(json.dumps(solve_itinerary(), indent=2))