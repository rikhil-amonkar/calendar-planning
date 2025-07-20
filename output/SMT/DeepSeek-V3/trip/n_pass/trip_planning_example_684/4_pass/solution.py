from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Edinburgh': ['Berlin', 'Amsterdam', 'Brussels'],
        'Amsterdam': ['Berlin', 'Edinburgh', 'Reykjavik', 'Vienna'],
        'Berlin': ['Edinburgh', 'Amsterdam', 'Vienna', 'Brussels', 'Reykjavik'],
        'Vienna': ['Berlin', 'Reykjavik', 'Brussels', 'Amsterdam'],
        'Brussels': ['Berlin', 'Edinburgh', 'Vienna', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Amsterdam', 'Brussels', 'Berlin']
    }
    
    # Create Z3 solver
    s = Solver()
    
    # Variables: for each day (1..23), which city (0..5)
    day_to_city = [Int(f'day_{day}_city') for day in range(1, 24)]
    
    # Each day's variable must be between 0 and 5
    for day in range(23):
        s.add(day_to_city[day] >= 0, day_to_city[day] <= 5)
    
    # Constraint: consecutive cities must have a direct flight
    for day in range(22):  # days 1..22, next is day+1 (2..23)
        current_city = day_to_city[day]
        next_city = day_to_city[day + 1]
        # Encode that next_city is in direct_flights of current_city
        # We create a disjunction over all possible direct flights from current_city
        possible_next = []
        for city in cities:
            current_idx = city_to_idx[city]
            for neighbor in direct_flights[city]:
                neighbor_idx = city_to_idx[neighbor]
                possible_next.append(And(current_city == current_idx, next_city == neighbor_idx))
        s.add(Or(possible_next))
    
    # Total days per city
    amsterdam_days = Sum([If(day_to_city[day] == city_to_idx['Amsterdam'], 1, 0) for day in range(23)])
    edinburgh_days = Sum([If(day_to_city[day] == city_to_idx['Edinburgh'], 1, 0) for day in range(23)])
    brussels_days = Sum([If(day_to_city[day] == city_to_idx['Brussels'], 1, 0) for day in range(23)])
    vienna_days = Sum([If(day_to_city[day] == city_to_idx['Vienna'], 1, 0) for day in range(23)])
    berlin_days = Sum([If(day_to_city[day] == city_to_idx['Berlin'], 1, 0) for day in range(23)])
    reykjavik_days = Sum([If(day_to_city[day] == city_to_idx['Reykjavik'], 1, 0) for day in range(23)])
    
    s.add(amsterdam_days == 4)
    s.add(edinburgh_days == 5)
    s.add(brussels_days == 5)
    s.add(vienna_days == 5)
    s.add(berlin_days == 4)
    s.add(reykjavik_days == 5)
    
    # Specific date ranges: Amsterdam between day 5-8 (days are 1-based, so indices 4..7)
    s.add(Or([day_to_city[day] == city_to_idx['Amsterdam'] for day in range(4, 8)]))  # at least one day in 5-8
    
    # Berlin between day 16-19 (indices 15..18)
    s.add(Or([day_to_city[day] == city_to_idx['Berlin'] for day in range(15, 19)]))
    
    # Reykjavik between day 12-16 (indices 11..15)
    s.add(Or([day_to_city[day] == city_to_idx['Reykjavik'] for day in range(11, 16)]))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(23):
            city_idx = m.evaluate(day_to_city[day]).as_long()
            itinerary.append({'day': day + 1, 'city': cities[city_idx]})
        
        # Verify constraints are met
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['city']] += 1
        
        # Verify specific date ranges
        amsterdam_in_range = any(5 <= entry['day'] <= 8 and entry['city'] == 'Amsterdam' for entry in itinerary)
        berlin_in_range = any(16 <= entry['day'] <= 19 and entry['city'] == 'Berlin' for entry in itinerary)
        reykjavik_in_range = any(12 <= entry['day'] <= 16 and entry['city'] == 'Reykjavik' for entry in itinerary)
        
        # Verify direct flights between consecutive cities
        valid_flights = True
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i + 1]['city']
            if next_city not in direct_flights[current_city]:
                valid_flights = False
                break
        
        if (city_counts['Amsterdam'] == 4 and city_counts['Edinburgh'] == 5 and
            city_counts['Brussels'] == 5 and city_counts['Vienna'] == 5 and
            city_counts['Berlin'] == 4 and city_counts['Reykjavik'] == 5 and
            amsterdam_in_range and berlin_in_range and reykjavik_in_range and valid_flights):
            return {'itinerary': itinerary}
        else:
            print("Generated itinerary does not meet all constraints.")
            return None
    else:
        print("No solution found.")
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    import json
    print(json.dumps(itinerary, indent=2))