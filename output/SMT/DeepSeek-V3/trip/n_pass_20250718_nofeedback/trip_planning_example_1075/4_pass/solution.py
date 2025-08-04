from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    # Direct flight connections
    direct_flights = {
        'Reykjavik': ['Stuttgart', 'Vienna'],
        'Stuttgart': ['Split', 'Vienna', 'Edinburgh', 'Manchester'],
        'Prague': ['Manchester', 'Edinburgh', 'Vienna', 'Split', 'Lyon', 'Reykjavik'],
        'Edinburgh': ['Prague', 'Stuttgart'],
        'Manchester': ['Split', 'Prague', 'Vienna'],
        'Vienna': ['Stuttgart', 'Prague', 'Manchester', 'Lyon', 'Split', 'Reykjavik'],
        'Split': ['Stuttgart', 'Manchester', 'Prague', 'Lyon', 'Vienna'],
        'Lyon': ['Vienna', 'Split', 'Prague']
    }
    
    # Create a reverse mapping for flights (undirected)
    flight_pairs = set()
    for city, destinations in direct_flights.items():
        for dest in destinations:
            if (dest, city) not in flight_pairs:
                flight_pairs.add((city, dest))
    
    total_days = 25
    days = range(1, total_days + 1)
    
    # Create Z3 variables: day[i] is the city on day i
    day_vars = [Int(f'day_{i}') for i in days]
    
    # Create a mapping from city to index
    city_index = {city: idx for idx, city in enumerate(cities.keys())}
    index_city = {idx: city for city, idx in city_index.items()}
    
    s = Solver()
    
    # Each day must be assigned a city index (0 to 7)
    for d in day_vars:
        s.add(And(d >= 0, d < len(cities)))
    
    # Constraint: Edinburgh must be visited from day 5 to day 8 (inclusive)
    edinburgh_idx = city_index['Edinburgh']
    for day in range(5, 9):
        s.add(day_vars[day - 1] == edinburgh_idx)
    
    # Constraint: Split must be visited between day 19 and day 23 (inclusive)
    split_idx = city_index['Split']
    s.add(Or([day_vars[day - 1] == split_idx for day in range(19, 24)]))
    
    # Constraints for city days
    for city, req_days in cities.items():
        city_idx = city_index[city]
        s.add(Sum([If(day_vars[i] == city_idx, 1, 0) for i in range(total_days)]) == req_days)
    
    # Flight constraints: consecutive days must be either same city or connected by a flight
    for i in range(total_days - 1):
        current_city_var = day_vars[i]
        next_city_var = day_vars[i + 1]
        # Either stay in the same city or move to a connected city
        same_city = (current_city_var == next_city_var)
        possible_flights = []
        current_city = index_city[model.eval(current_city_var).as_long()] if s.check() == sat else None
        next_city = index_city[model.eval(next_city_var).as_long()] if s.check() == sat else None
        if current_city and next_city and current_city != next_city:
            assert (current_city, next_city) in flight_pairs or (next_city, current_city) in flight_pairs, \
                f"No flight from {current_city} to {next_city} on day {i+1}"
        s.add(Or(same_city, Or([And(current_city_var == city_index[city], next_city_var == city_index[other_city]) 
                              for city in cities for other_city in cities 
                              if (city, other_city) in flight_pairs or (other_city, city) in flight_pairs])))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, total_days + 1):
            day_var = day_vars[day - 1]
            city_idx = model.eval(day_var).as_long()
            city = index_city[city_idx]
            itinerary.append({'day': day, 'city': city})
        
        # Verify the solution meets all constraints
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['city']] += 1
        
        for city, req in cities.items():
            assert city_days[city] == req, f"City {city} has {city_days[city]} days, expected {req}"
        
        # Verify Edinburgh days 5-8
        for day in range(5, 9):
            assert itinerary[day - 1]['city'] == 'Edinburgh', f"Day {day} should be Edinburgh"
        
        # Verify Split has at least one day between 19-23
        split_in_wedding_days = False
        for day in range(19, 24):
            if itinerary[day - 1]['city'] == 'Split':
                split_in_wedding_days = True
                break
        assert split_in_wedding_days, "Split not visited during wedding days 19-23"
        
        # Verify flight connections
        for i in range(total_days - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i + 1]['city']
            if current_city != next_city:
                assert (current_city, next_city) in flight_pairs or (next_city, current_city) in flight_pairs, \
                    f"No flight from {current_city} to {next_city} on day {i+1}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))