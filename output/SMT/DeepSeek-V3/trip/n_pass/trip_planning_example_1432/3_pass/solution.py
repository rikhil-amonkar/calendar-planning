import json
from z3 import *

def solve_itinerary():
    # Cities to visit
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 'Valencia', 
              'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    
    # Direct flights as per the problem statement
    direct_flights = {
        'Valencia': ['Frankfurt', 'Athens', 'Bucharest', 'Vienna', 'Amsterdam'],
        'Vienna': ['Bucharest', 'Riga', 'Frankfurt', 'Athens', 'Amsterdam', 'Stockholm', 'Reykjavik', 'Valencia'],
        'Athens': ['Valencia', 'Bucharest', 'Riga', 'Stockholm', 'Frankfurt', 'Vienna', 'Amsterdam', 'Reykjavik'],
        'Riga': ['Frankfurt', 'Bucharest', 'Vienna', 'Amsterdam', 'Stockholm', 'Athens'],
        'Bucharest': ['Vienna', 'Athens', 'Amsterdam', 'Frankfurt', 'Valencia', 'Riga'],
        'Frankfurt': ['Valencia', 'Riga', 'Amsterdam', 'Salzburg', 'Bucharest', 'Stockholm', 'Vienna', 'Athens', 'Reykjavik'],
        'Salzburg': ['Frankfurt'],
        'Reykjavik': ['Amsterdam', 'Frankfurt', 'Athens', 'Stockholm', 'Vienna'],
        'Amsterdam': ['Bucharest', 'Frankfurt', 'Valencia', 'Vienna', 'Reykjavik', 'Stockholm', 'Riga', 'Athens'],
        'Stockholm': ['Athens', 'Vienna', 'Amsterdam', 'Riga', 'Frankfurt', 'Reykjavik']
    }
    
    # Required days in each city
    required_days = {
        'Frankfurt': 4,
        'Salzburg': 5,
        'Athens': 5,
        'Reykjavik': 5,
        'Bucharest': 3,
        'Valencia': 2,
        'Vienna': 5,
        'Amsterdam': 3,
        'Stockholm': 3,
        'Riga': 3
    }
    
    # Fixed events
    fixed_events = [
        ('Stockholm', 1, 3),  # Meet friend in Stockholm between day 1-3
        ('Valencia', 5, 6),    # Annual show in Valencia on day 5-6
        ('Vienna', 6, 10),     # Wedding in Vienna between day 6-10
        ('Athens', 14, 18),    # Workshop in Athens between day 14-18
        ('Riga', 18, 20)       # Conference in Riga between day 18-20
    ]
    
    # Create Z3 solver
    s = Solver()
    
    # Create variables: for each day (1..29), which city are we in?
    day_city = [Int(f'day_{i}_city') for i in range(1, 30)]
    
    # Map each city to an integer
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints: each day's variable must be a valid city index
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Fixed events constraints
    for city, start_day, end_day in fixed_events:
        city_idx = city_to_int[city]
        for day in range(start_day, end_day + 1):
            s.add(day_city[day - 1] == city_idx)
    
    # For other cities, ensure the total days meet requirements.
    for city in cities:
        city_idx = city_to_int[city]
        total_days = Sum([If(day_city[i] == city_idx, 1, 0) for i in range(29)])
        s.add(total_days == required_days[city])
    
    # Flight transitions: if day i and i+1 are different, there must be a direct flight
    for i in range(28):
        current_day = day_city[i]
        next_day = day_city[i + 1]
        # If cities are different, check flight exists
        s.add(Implies(current_day != next_day, 
                      Or([And(current_day == city_to_int[city_from], 
                               next_day == city_to_int[city_to])
                          for city_from in direct_flights 
                          for city_to in direct_flights[city_from]])))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(29):
            day = i + 1
            city_idx = m.evaluate(day_city[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": day, "place": city})
        
        # Verify that all constraints are met (debugging)
        # Check total days per city
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city in cities:
            assert city_days[city] == required_days[city], f"City {city} has {city_days[city]} days, expected {required_days[city]}"
        
        # Check flight transitions
        for i in range(28):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current_city != next_city:
                assert next_city in direct_flights[current_city], f"No direct flight from {current_city} to {next_city} on day {i+1}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))