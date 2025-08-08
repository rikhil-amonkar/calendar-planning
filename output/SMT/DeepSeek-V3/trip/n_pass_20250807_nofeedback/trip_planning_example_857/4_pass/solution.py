from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Hamburg', 'Frankfurt'),
        ('Naples', 'Mykonos'),
        ('Hamburg', 'Porto'),
        ('Hamburg', 'Geneva'),
        ('Mykonos', 'Geneva'),
        ('Frankfurt', 'Geneva'),
        ('Frankfurt', 'Porto'),
        ('Geneva', 'Porto'),
        ('Geneva', 'Manchester'),
        ('Naples', 'Manchester'),
        ('Frankfurt', 'Naples'),
        ('Frankfurt', 'Manchester'),
        ('Naples', 'Geneva'),
        ('Porto', 'Manchester'),
        ('Hamburg', 'Manchester')
    ]
    
    # Create bidirectional flights
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(18)]
    
    # Each day must be one of the cities (0 to 6)
    for day in days:
        s.add(day >= 0, day < 7)
    
    # Flight constraints: consecutive days must be either same city or have a direct flight
    for i in range(17):
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a city with a direct flight
        same_city = (current_day == next_day)
        flight_possible = Or([And(current_day == city_map[a], next_day == city_map[b]) for (a, b) in all_flights])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints
    # Porto: 2 days
    porto_days = Sum([If(days[i] == city_map['Porto'], 1, 0) for i in range(18)])
    s.add(porto_days == 2)
    
    # Geneva: 3 days
    geneva_days = Sum([If(days[i] == city_map['Geneva'], 1, 0) for i in range(18)])
    s.add(geneva_days == 3)
    
    # Mykonos: 3 days, with at least one day between day 10 and 12 (inclusive)
    mykonos_days = Sum([If(days[i] == city_map['Mykonos'], 1, 0) for i in range(18)])
    s.add(mykonos_days == 3)
    # At least one day in Mykonos between day 10 and 12 (1-based, so indices 9 to 11)
    s.add(Or([days[i] == city_map['Mykonos'] for i in range(9, 12)]))
    
    # Manchester: 4 days, with wedding between day 15-18 (must be in Manchester at least one of these days)
    manchester_days = Sum([If(days[i] == city_map['Manchester'], 1, 0) for i in range(18)])
    s.add(manchester_days == 4)
    # Must be in Manchester on at least one day between 15-18 (indices 14-17)
    s.add(Or([days[i] == city_map['Manchester'] for i in range(14, 18)]))
    
    # Hamburg: 5 days
    hamburg_days = Sum([If(days[i] == city_map['Hamburg'], 1, 0) for i in range(18)])
    s.add(hamburg_days == 5)
    
    # Naples: 5 days
    naples_days = Sum([If(days[i] == city_map['Naples'], 1, 0) for i in range(18)])
    s.add(naples_days == 5)
    
    # Frankfurt: 2 days, with show on day 5-6 (indices 4-5 in 0-based)
    frankfurt_days = Sum([If(days[i] == city_map['Frankfurt'], 1, 0) for i in range(18)])
    s.add(frankfurt_days == 2)
    s.add(Or(days[4] == city_map['Frankfurt'], days[5] == city_map['Frankfurt']))
    
    # Additional constraints to ensure the itinerary is feasible
    # Ensure that the days in each city are contiguous where possible
    # For example, if a city is visited for multiple days, those days should be consecutive
    # This is not strictly necessary but can help in finding a solution faster
    for city in cities:
        city_idx = city_map[city]
        # Find all days where the city is visited
        city_days = [days[i] == city_idx for i in range(18)]
        # Ensure that the city days are contiguous
        # This is a soft constraint and can be commented out if it causes issues
        for i in range(17):
            s.add(Implies(And(city_days[i], Not(city_days[i+1])), Not(Or(city_days[i+2:]))))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(18):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))