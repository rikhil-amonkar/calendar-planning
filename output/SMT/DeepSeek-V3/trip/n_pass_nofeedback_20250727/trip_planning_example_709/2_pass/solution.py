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
    
    # Direct flights: adjacency list
    direct_flights = {
        'Helsinki': ['Prague', 'Reykjavik', 'Dubrovnik'],
        'Prague': ['Helsinki', 'Valencia', 'Reykjavik'],
        'Valencia': ['Prague', 'Porto'],
        'Porto': ['Valencia'],
        'Reykjavik': ['Helsinki', 'Prague'],
        'Dubrovnik': ['Helsinki']
    }
    
    # Days are 1..18
    days = 18
    day_numbers = range(1, days + 1)
    
    # Create a Z3 solver
    s = Solver()
    
    # Create variables: for each day, which city are we in?
    city_vars = [Int(f'day_{i}') for i in day_numbers]
    
    # Assign each city a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraint: each day's variable must be one of the city IDs
    for day in city_vars:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraint: transitions between cities must be via direct flights
    for i in range(days - 1):
        current_day = city_vars[i]
        next_day = city_vars[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            *[And(current_day == city_ids[city], next_day == city_ids[neighbor])
              for city in direct_flights
              for neighbor in direct_flights[city]]
        ))
    
    # Constraint: count days in each city
    for city in cities:
        required_days = cities[city]
        city_id = city_ids[city]
        # The sum of days where city_var is this city's ID must equal required_days
        s.add(Sum([If(city_vars[i] == city_id, 1, 0) for i in range(days)]) == required_days)
    
    # Porto must be visited between day 16 and 18 (inclusive)
    porto_id = city_ids['Porto']
    s.add(Or([city_vars[i] == porto_id for i in range(15, 18)]))  # days are 1-based; indices 15,16,17 are days 16,17,18
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(days):
            city_id = model.evaluate(city_vars[day]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': day + 1, 'place': city})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should have ensured it)
        city_days = {city: 0 for city in cities}
        prev_city = None
        valid = True
        for entry in itinerary:
            day = entry['day']
            city = entry['place']
            city_days[city] += 1
            if prev_city is not None and prev_city != city:
                if city not in direct_flights[prev_city]:
                    valid = False
                    print(f"Invalid flight from {prev_city} to {city} on day {day}")
            prev_city = city
        
        for city in cities:
            if city_days[city] != cities[city]:
                print(f"City {city} has {city_days[city]} days instead of {cities[city]}")
                valid = False
        
        porto_visited = False
        for day in range(16, 19):
            if itinerary[day - 1]['place'] == 'Porto':
                porto_visited = True
        if not porto_visited:
            print("Porto not visited between days 16-18")
            valid = False
        
        if not valid:
            print("Generated itinerary does not meet constraints")
            return None
        
        return {'itinerary': itinerary}
    else:
        print("No solution found")
        return None

# Generate and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    import json
    print(json.dumps(itinerary, indent=2))