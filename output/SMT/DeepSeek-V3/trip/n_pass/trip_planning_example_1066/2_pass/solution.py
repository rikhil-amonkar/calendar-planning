import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Direct flights (undirected)
    direct_flights = {
        'Brussels': ['London', 'Bucharest', 'Madrid', 'Helsinki'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Stuttgart': ['London', 'Split'],
        'Mykonos': ['Madrid', 'London'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Bucharest', 'Mykonos', 'Brussels'],
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Mykonos', 'Stuttgart', 'Split']
    }
    
    # Correcting 'Madrid' typo
    direct_flights['Madrid'] = direct_flights.pop('Madrid', ['Split', 'Helsinki', 'London', 'Bucharest', 'Mykonos', 'Brussels'])
    
    # Total days
    total_days = 21
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: for each day, which city are we in?
    day_to_city = [Int(f'day_{day}_city') for day in range(1, total_days + 1)]
    
    # Create a mapping from city names to integers
    city_list = list(cities.keys())
    city_ids = {city: idx for idx, city in enumerate(city_list)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraint: each day's variable must be a valid city ID
    for day_var in day_to_city:
        solver.add(day_var >= 0, day_var < len(city_list))
    
    # Constraint: consecutive days must be either the same city or connected by a direct flight
    for day in range(total_days - 1):
        current_city_var = day_to_city[day]
        next_city_var = day_to_city[day + 1]
        # Either stay in the same city or move to a connected city
        solver.add(Or(
            current_city_var == next_city_var,
            *[And(current_city_var == city_ids[city], next_city_var == city_ids[neighbor])
              for city in city_list
              for neighbor in direct_flights[city]]
        ))
    
    # Constraints for the required days in each city
    for city, required_days in cities.items():
        city_id = city_ids[city]
        solver.add(Sum([If(day_to_city[day] == city_id, 1, 0) for day in range(total_days)]) == required_days
    
    # Additional constraints:
    # 1. Stuttgart must be visited between day 1 and day 4 (at least one day in this interval)
    stuttgart_id = city_ids['Stuttgart']
    solver.add(Or([day_to_city[day] == stuttgart_id for day in range(0, 4)]))
    
    # 2. Madrid must be on day 20 and 21 (1-based: days 19 and 20 in 0-based)
    madrid_id = city_ids['Madrid']
    solver.add(day_to_city[19] == madrid_id)
    solver.add(day_to_city[20] == madrid_id)
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(1, total_days + 1):
            city_id = model.evaluate(day_to_city[day - 1]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': day, 'place': city})
        
        # Format the output as JSON
        output = {'itinerary': itinerary}
        return output
    else:
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print("No valid itinerary found.")