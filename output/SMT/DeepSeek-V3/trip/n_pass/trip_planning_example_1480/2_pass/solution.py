from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,
        'Madrid': 4,
        'Vilnius': 4,
        'Venice': 5,
        'Geneva': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    # Direct flights represented as a set of tuples
    direct_flights = {
        ('Munich', 'Vienna'),
        ('Istanbul', 'Brussels'),
        ('Vienna', 'Vilnius'),
        ('Madrid', 'Munich'),
        ('Venice', 'Brussels'),
        ('Riga', 'Brussels'),
        ('Geneva', 'Istanbul'),
        ('Munich', 'Reykjavik'),
        ('Vienna', 'Istanbul'),
        ('Riga', 'Istanbul'),
        ('Reykjavik', 'Vienna'),
        ('Venice', 'Munich'),
        ('Madrid', 'Venice'),
        ('Vilnius', 'Istanbul'),
        ('Venice', 'Vienna'),
        ('Venice', 'Istanbul'),
        ('Reykjavik', 'Madrid'),
        ('Riga', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Reykjavik', 'Brussels'),
        ('Vilnius', 'Brussels'),
        ('Vilnius', 'Munich'),
        ('Madrid', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Geneva', 'Vienna'),
        ('Geneva', 'Brussels'),
        ('Geneva', 'Madrid'),
        ('Geneva', 'Munich'),
        ('Madrid', 'Brussels'),
        ('Vienna', 'Brussels'),
        ('Madrid', 'Istanbul'),
        ('Riga', 'Vilnius')
    }
    
    # Make flights bidirectional
    bidirectional_flights = set()
    for (a, b) in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    # Create Z3 variables: day[i] represents the city on day i (1-based)
    days = 27
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Solver
    s = Solver()
    
    # Each day variable must be one of the city IDs
    for day in day_vars:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraints for total days per city
    for city, total_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day == city_id, 1, 0) for day in day_vars]) == total_days)
    
    # Specific constraints:
    # Geneva between day 1 and day 4
    for i in range(1, 5):
        s.add(day_vars[i-1] == city_ids['Geneva'])
    
    # Venice workshop between day 7 and day 11 (5 days)
    for i in range(7, 12):
        s.add(day_vars[i-1] == city_ids['Venice'])
    
    # Vilnius friends between day 20 and 23 (4 days)
    for i in range(20, 24):
        s.add(day_vars[i-1] == city_ids['Vilnius'])
    
    # Brussels wedding on day 26 and 27
    s.add(day_vars[25] == city_ids['Brussels'])
    s.add(day_vars[26] == city_ids['Brussels'])
    
    # Flight connectivity: consecutive days must be either same city or have a direct flight
    for i in range(days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        # Either same city or connected by flight
        same_city = (current_day == next_day)
        flight_possible = Or([And(current_day == city_ids[a], next_day == city_ids[b]) 
                            for (a, b) in direct_flights])
        s.add(Or(same_city, flight_possible))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, days + 1):
            day_var = day_vars[i-1]
            city_id = model[day_var].as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': i, 'place': city})
        
        # Verify the itinerary meets all constraints
        # (This is a sanity check; Z3 should have ensured it)
        # Return as JSON
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({'error': 'No solution found'}, indent=2)

# Execute the solver and print the result
print(solve_itinerary())