from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Stockholm': 3,
        'Hamburg': 5,
        'Florence': 2,
        'Istanbul': 5,
        'Oslo': 5,
        'Vilnius': 5,
        'Santorini': 2,
        'Munich': 5,
        'Frankfurt': 4,
        'Krakow': 5
    }
    
    # Direct flights as a dictionary: key is source, value is list of destinations
    direct_flights = {
        'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Vilnius', 'Frankfurt', 'Hamburg', 'Munich'],
        'Stockholm': ['Oslo', 'Istanbul', 'Munich', 'Hamburg', 'Frankfurt', 'Santorini', 'Krakow'],
        'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Oslo', 'Munich', 'Stockholm'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Oslo', 'Florence', 'Stockholm', 'Munich', 'Hamburg', 'Vilnius'],
        'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Frankfurt', 'Florence', 'Krakow', 'Vilnius'],
        'Hamburg': ['Stockholm', 'Istanbul', 'Munich', 'Oslo', 'Frankfurt'],
        'Istanbul': ['Krakow', 'Oslo', 'Stockholm', 'Vilnius', 'Frankfurt', 'Munich', 'Hamburg'],
        'Vilnius': ['Istanbul', 'Krakow', 'Oslo', 'Frankfurt', 'Munich'],
        'Florence': ['Frankfurt', 'Munich'],
        'Santorini': ['Stockholm', 'Oslo']
    }
    
    # Fixed events
    fixed_events = {
        'Krakow': (5, 9),
        'Istanbul': (25, 29)
    }
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create a variable for each day (1..32), representing the city visited
    day_vars = [Int(f'day_{i}') for i in range(1, 33)]
    
    # Map city names to integer indices (for Z3)
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraints for each day to be one of the city IDs
    for day in day_vars:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Fixed events constraints
    for city, (start, end) in fixed_events.items():
        for day in range(start, end + 1):
            s.add(day_vars[day - 1] == city_ids[city])
    
    # Constraints for total days in each city
    for city, days in cities.items():
        s.add(Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(32)]) == days)
    
    # Constraints for valid transitions between cities
    for i in range(31):  # days 1..31 transitioning to next day
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            *[And(current_day == city_ids[src], next_day == city_ids[dst]) 
              for src in direct_flights for dst in direct_flights[src]]
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(32):
            day_num = i + 1
            city_id = m.evaluate(day_vars[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the itinerary meets all constraints
        # (This is a basic check; more thorough verification can be done)
        itinerary_json = {'itinerary': itinerary}
        return itinerary_json
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))