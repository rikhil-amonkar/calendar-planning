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
    
    # Corrected direct flights (undirected)
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
    
    # Total days
    total_days = 21
    
    # Create Z3 solver
    solver = Solver()
    
    # Create variables for each day's city
    day_to_city = [Int(f'day_{day}') for day in range(1, total_days+1)]
    
    # City to ID mapping
    city_list = list(cities.keys())
    city_ids = {city: idx for idx, city in enumerate(city_list)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Each day must be a valid city
    for day in day_to_city:
        solver.add(day >= 0, day < len(city_list))
    
    # Flight connections between consecutive days
    for i in range(total_days-1):
        current = day_to_city[i]
        next_day = day_to_city[i+1]
        
        # Generate all possible flight connections
        flight_options = []
        for city in city_list:
            for neighbor in direct_flights[city]:
                flight_options.append(And(current == city_ids[city], next_day == city_ids[neighbor]))
        
        # Either stay or move to connected city
        solver.add(Or(current == next_day, *flight_options))
    
    # Total days per city
    for city, days in cities.items():
        solver.add(Sum([If(day == city_ids[city], 1, 0) for day in day_to_city]) == days)
    
    # Specific constraints
    stuttgart_id = city_ids['Stuttgart']
    solver.add(Or([day_to_city[i] == stuttgart_id for i in range(4)]))  # Days 1-4
    
    madrid_id = city_ids['Madrid']
    solver.add(day_to_city[19] == madrid_id)  # Day 20
    solver.add(day_to_city[20] == madrid_id)  # Day 21
    
    # Solve
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(1, total_days+1):
            city_id = model.evaluate(day_to_city[day-1]).as_long()
            itinerary.append({'day': day, 'place': id_to_city[city_id]})
        return {'itinerary': itinerary}
    else:
        return None

# Execute and print result
result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found")