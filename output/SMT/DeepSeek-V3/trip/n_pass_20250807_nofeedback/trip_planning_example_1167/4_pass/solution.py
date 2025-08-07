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

    # Corrected direct flights (bidirectional)
    direct_flights = [
        ('Dublin', 'Brussels'), ('Mykonos', 'Naples'), ('Venice', 'Istanbul'),
        ('Frankfurt', 'Krakow'), ('Naples', 'Dublin'), ('Krakow', 'Brussels'),
        ('Naples', 'Istanbul'), ('Naples', 'Brussels'), ('Istanbul', 'Frankfurt'),
        ('Brussels', 'Frankfurt'), ('Istanbul', 'Krakow'), ('Istanbul', 'Brussels'),
        ('Venice', 'Frankfurt'), ('Naples', 'Frankfurt'), ('Dublin', 'Krakow'),
        ('Venice', 'Brussels'), ('Naples', 'Venice'), ('Istanbul', 'Dublin'),
        ('Venice', 'Dublin'), ('Dublin', 'Frankfurt')
    ]

    # Create flight connections graph
    flight_graph = {city: set() for city in city_names}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)

    # Create Z3 variables: X[i] = city index for day i (0-based)
    days = 21
    X = [Int(f'X_{i}') for i in range(days)]
    s = Solver()

    # Each day must be a valid city index
    for i in range(days):
        s.add(X[i] >= 0, X[i] < len(city_names))

    # Flight transitions between consecutive days
    for i in range(days - 1):
        current_city = X[i]
        next_city = X[i + 1]
        # Either stay in same city or move to connected city
        same_city = current_city == next_city
        flight_options = []
        for city in city_names:
            for neighbor in flight_graph[city]:
                flight_options.append(And(current_city == city_to_idx[city], 
                                        next_city == city_to_idx[neighbor]))
        s.add(Or(same_city, Or(flight_options)))

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

    # Solve and format output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(X[i]).as_long()
            itinerary.append({'day': i + 1, 'city': city_names[city_idx]})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in city_names}
        for entry in itinerary:
            city_days[entry['city']] += 1
        
        for city, required in cities.items():
            assert city_days[city] == required, f"{city} days mismatch"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))