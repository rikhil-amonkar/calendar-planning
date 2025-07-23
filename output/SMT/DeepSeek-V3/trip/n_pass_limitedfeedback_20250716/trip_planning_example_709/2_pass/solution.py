import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    
    # Direct flights as a graph
    flights = {
        'Helsinki': ['Prague', 'Reykjavik', 'Dubrovnik'],
        'Prague': ['Helsinki', 'Valencia', 'Reykjavik'],
        'Valencia': ['Prague', 'Porto'],
        'Porto': ['Valencia'],
        'Reykjavik': ['Helsinki', 'Prague'],
        'Dubrovnik': ['Helsinki']
    }
    
    # Total days
    total_days = 18
    
    # Create a Z3 solver
    s = Solver()
    
    # Create variables: day[i] represents the city on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(total_days)]
    
    # Map each city to an integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Add constraints that each day is assigned a valid city id
    for d in day:
        s.add(Or([d == idx for idx in city_ids.values()]))
    
    # Constraint: transitions between cities must be via direct flights
    for i in range(total_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # The next city must be in the current city's flight list or the same city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[c], next_city == city_ids[n]) 
              for c in flights for n in flights[c]]
        ))
    
    # Constraint: total days per city must match requirements
    for city, required_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day[i] == city_id, 1, 0) for i in range(total_days)]) == required_days
    
    # Constraint: Porto must be visited between day 16 and 18 (1-based)
    porto_id = city_ids['Porto']
    s.add(Or([day[i] == porto_id for i in range(15, 18)]))  # days 16-18 are indices 15-17
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Generate the itinerary by listing each day's city
        for i in range(total_days):
            city_id = model.evaluate(day[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': i + 1, 'place': city})
        
        # Prepare the output
        output = {'itinerary': itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No valid itinerary found.")

solve_itinerary()