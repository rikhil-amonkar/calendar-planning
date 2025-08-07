from z3 import *

def solve_itinerary():
    # Cities with their required visit days
    cities = {
        'Dublin': 5,
        'Krakow': 4,
        'Istanbul': 3,
        'Venice': 3,
        'Naples': 4,
        'Brussels': 2,
        'Mykonos': 4,
        'Frankfurt': 3
    }
    city_names = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_names)}

    # Complete flight connections (bidirectional)
    flight_connections = [
        ('Dublin', 'Brussels'),
        ('Dublin', 'Krakow'),
        ('Dublin', 'Frankfurt'),
        ('Dublin', 'Naples'),
        ('Dublin', 'Istanbul'),
        ('Dublin', 'Venice'),
        ('Brussels', 'Frankfurt'),
        ('Brussels', 'Krakow'),
        ('Brussels', 'Naples'),
        ('Brussels', 'Istanbul'),
        ('Brussels', 'Venice'),
        ('Frankfurt', 'Krakow'),
        ('Frankfurt', 'Istanbul'),
        ('Frankfurt', 'Venice'),
        ('Frankfurt', 'Naples'),
        ('Krakow', 'Istanbul'),
        ('Istanbul', 'Venice'),
        ('Istanbul', 'Naples'),
        ('Venice', 'Naples'),
        ('Naples', 'Mykonos')
    ]

    # Create flight graph
    flight_graph = {city: set() for city in city_names}
    for a, b in flight_connections:
        if a in city_names and b in city_names:
            flight_graph[a].add(b)
            flight_graph[b].add(a)

    # Create Z3 variables
    days = 21
    X = [Int(f'X_{i}') for i in range(days)]
    s = Solver()

    # Each day must be a valid city
    for i in range(days):
        s.add(X[i] >= 0, X[i] < len(city_names))

    # Flight transitions between days
    for i in range(days - 1):
        current = X[i]
        next_city = X[i + 1]
        # Can stay or fly to connected city
        stay = current == next_city
        fly_options = []
        for city in city_names:
            for neighbor in flight_graph[city]:
                fly_options.append(And(current == city_to_idx[city], 
                                    next_city == city_to_idx[neighbor]))
        s.add(Or(stay, Or(fly_options)))

    # Duration constraints
    for city, days_needed in cities.items():
        idx = city_to_idx[city]
        s.add(Sum([If(X[i] == idx, 1, 0) for i in range(days)]) == days_needed)

    # Specific date constraints
    # Dublin must be days 11-15 (0-based 10-14)
    dublin_idx = city_to_idx['Dublin']
    for i in range(10, 15):
        s.add(X[i] == dublin_idx)

    # Istanbul between day 9-11 (0-based 8-10)
    istanbul_idx = city_to_idx['Istanbul']
    s.add(Or([X[i] == istanbul_idx for i in range(8, 11)]))

    # Mykonos between day 1-4 (0-based 0-3)
    mykonos_idx = city_to_idx['Mykonos']
    s.add(Or([X[i] == mykonos_idx for i in range(0, 4)]))

    # Frankfurt between day 15-17 (0-based 14-16)
    frankfurt_idx = city_to_idx['Frankfurt']
    s.add(Or([X[i] == frankfurt_idx for i in range(14, 17)]))

    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(X[i]).as_long()
            itinerary.append({'day': i + 1, 'city': city_names[city_idx]})
        
        # Verify solution
        city_counts = {city: 0 for city in city_names}
        for entry in itinerary:
            city_counts[entry['city']] += 1
        
        for city, required in cities.items():
            assert city_counts[city] == required, f"{city} day count mismatch"
        
        # Verify date ranges
        assert all(itinerary[i]['city'] == 'Dublin' for i in range(10, 15))
        assert any(itinerary[i]['city'] == 'Istanbul' for i in range(8, 11))
        assert any(itinerary[i]['city'] == 'Mykonos' for i in range(0, 4))
        assert any(itinerary[i]['city'] == 'Frankfurt' for i in range(14, 17))
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))