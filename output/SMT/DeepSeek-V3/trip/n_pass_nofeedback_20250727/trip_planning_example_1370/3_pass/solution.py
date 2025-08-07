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
            if neighbor in city_ids:  # ensure neighbor is in our cities list
                connected_pairs.append((city_ids[city], city_ids[neighbor]))
    
    # Specific constraints
    constraints = [
        ('Santorini', (25, 29)),  # Santorini between day 25 and 29
        ('Krakow', (18, 22)),      # Krakow between day 18 and 22
        ('Paris', (11, 15))        # Paris between day 11 and 15
    ]
    
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
    
    # Constraints for date ranges
    for city, (start, end) in constraints:
        city_id = city_ids[city]
        # All days in this city must be within the start-end range
        for i in range(30):
            solver.add(If(days[i] == city_id, And(i+1 >= start, i+1 <= end), True))
    
    # Flight connectivity constraints: consecutive days must be same city or connected by flight
    for i in range(29):  # days 1..29, next is i+1 (2..30)
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a connected city
        solver.add(Or(
            current_day == next_day,
            *[And(current_day == pair[0], next_day == pair[1]) for pair in connected_pairs]
        ))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(30):
            day_var = days[i]
            city_id = model[day_var].as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': i+1, 'place': city})
        
        # Convert to the required JSON format
        output = {'itinerary': itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))