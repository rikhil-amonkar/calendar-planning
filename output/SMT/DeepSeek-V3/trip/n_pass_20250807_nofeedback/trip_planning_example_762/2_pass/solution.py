from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (city1, city2)
    direct_flights = [
        ('London', 'Madrid'),
        ('Oslo', 'Vilnius'),
        ('Berlin', 'Vilnius'),
        ('Madrid', 'Oslo'),
        ('Madrid', 'Dublin'),
        ('London', 'Oslo'),
        ('Madrid', 'Berlin'),
        ('Berlin', 'Oslo'),
        ('Dublin', 'Oslo'),
        ('London', 'Dublin'),
        ('London', 'Berlin'),
        ('Berlin', 'Dublin')
    ]
    
    # Create a set of tuples representing direct flight connections (both directions)
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Number of days
    days = 13
    # Create Z3 variables: assign each day to a city (0..5)
    assignments = [Int(f"day_{i}") for i in range(days)]
    solver = Solver()
    
    # Each day's assignment must be between 0 and 5
    for day in assignments:
        solver.add(day >= 0, day < len(cities))
    
    # Constraints on the number of days per city
    city_days = [
        ('Dublin', 3),
        ('Madrid', 2),
        ('Oslo', 3),
        ('London', 2),
        ('Vilnius', 3),
        ('Berlin', 5)
    ]
    
    for city, required_days in city_days:
        city_idx = city_map[city]
        solver.add(Sum([If(assignments[i] == city_idx, 1, 0) for i in range(days)]) == required_days)
    
    # Dublin must include at least one day between 7-9 (1-based: days 6-8 in 0-based)
    solver.add(Or([assignments[i] == city_map['Dublin'] for i in range(6, 9)]))
    
    # Madrid must include day 2 or 3 (1-based: indices 1 or 2)
    solver.add(Or(assignments[1] == city_map['Madrid'], assignments[2] == city_map['Madrid']))
    
    # Berlin must include days 3-7 (1-based: indices 2-6)
    for i in range(2, 7):
        solver.add(assignments[i] == city_map['Berlin'])
    
    # Flight constraints: consecutive days must be either the same city or connected by a direct flight
    for i in range(days - 1):
        current_city = assignments[i]
        next_city = assignments[i+1]
        # Either same city or connected by a flight
        solver.add(Or(
            current_city == next_city,
            *[And(current_city == city_map[a], next_city == city_map[b]) for a, b in flight_pairs]
        ))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(assignments[i]).as_long()
            itinerary.append({"day": i+1, "city": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))