from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Santorini': 5,
        'Krakow': 5,
        'Paris': 5,
        'Vilnius': 3,
        'Munich': 5,
        'Geneva': 2,
        'Amsterdam': 4,
        'Budapest': 5,
        'Split': 4
    }
    
    # Direct flights as a graph (undirected)
    flight_graph = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Vilnius'],
        'Krakow': ['Paris', 'Split', 'Munich', 'Amsterdam', 'Vilnius'],
        'Vilnius': ['Munich', 'Split', 'Amsterdam', 'Paris', 'Krakow'],
        'Munich': ['Vilnius', 'Split', 'Amsterdam', 'Geneva', 'Krakow', 'Budapest', 'Paris'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Budapest', 'Santorini'],
        'Amsterdam': ['Paris', 'Geneva', 'Munich', 'Budapest', 'Split', 'Krakow', 'Vilnius', 'Santorini'],
        'Budapest': ['Amsterdam', 'Paris', 'Geneva', 'Munich'],
        'Split': ['Paris', 'Munich', 'Geneva', 'Amsterdam', 'Krakow', 'Vilnius'],
        'Santorini': ['Geneva', 'Amsterdam']
    }
    
    # Create connected city pairs
    connected_pairs = []
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    for city in flight_graph:
        for neighbor in flight_graph[city]:
            if neighbor in city_ids:
                connected_pairs.append((city_ids[city], city_ids[neighbor]))
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: day_1 to day_30, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 31)]
    
    # Each day variable must be one of the cities (encoded as integers)
    for day in days:
        solver.add(day >= 0, day < len(cities))
    
    # Constraints for city durations
    for city, duration in cities.items():
        city_id = city_ids[city]
        solver.add(Sum([If(day == city_id, 1, 0) for day in days]) == duration)
    
    # Special constraints for cities with date ranges
    # Paris must be between days 11-15 (5 consecutive days)
    solver.add(Or(
        *[And([days[i] == city_ids['Paris'] for i in range(10, 15)])  # Days 11-15
    ))
    
    # Krakow must be between days 18-22 (5 consecutive days)
    solver.add(Or(
        *[And([days[i] == city_ids['Krakow'] for i in range(17, 22)])  # Days 18-22
    ))
    
    # Santorini must be between days 25-29 (5 consecutive days)
    solver.add(Or(
        *[And([days[i] == city_ids['Santorini'] for i in range(24, 29)])  # Days 25-29
    ))
    
    # Flight connectivity constraints
    for i in range(29):  # For days 1-29
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or fly to connected city
        solver.add(Or(
            current == next_day,
            *[And(current == c1, next_day == c2) for (c1, c2) in connected_pairs]
        ))
    
    # Check if satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(30):
            day_var = days[i]
            city_id = model[day_var].as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': i+1, 'place': city})
        
        # Verify all constraints are met
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        for city, count in city_counts.items():
            assert count == cities[city], f"City {city} has wrong duration"
        
        # Verify date ranges
        paris_days = [i+1 for i in range(30) if itinerary[i]['place'] == 'Paris']
        assert all(11 <= d <= 15 for d in paris_days), "Paris days out of range"
        
        krakow_days = [i+1 for i in range(30) if itinerary[i]['place'] == 'Krakow']
        assert all(18 <= d <= 22 for d in krakow_days), "Krakow days out of range"
        
        santorini_days = [i+1 for i in range(30) if itinerary[i]['place'] == 'Santorini']
        assert all(25 <= d <= 29 for d in santorini_days), "Santorini days out of range"
        
        # Verify flight connections
        for i in range(29):
            current = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current != next_city:
                assert next_city in flight_graph[current], f"No flight from {current} to {next_city}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))