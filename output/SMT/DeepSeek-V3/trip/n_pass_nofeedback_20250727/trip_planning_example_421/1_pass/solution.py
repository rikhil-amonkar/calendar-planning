from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Nice', 'Krakow', 'Dublin', 'Lyon', 'Frankfurt']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Nice': ['Dublin', 'Frankfurt', 'Lyon'],
        'Dublin': ['Nice', 'Frankfurt', 'Krakow', 'Lyon'],
        'Krakow': ['Dublin', 'Frankfurt'],
        'Lyon': ['Frankfurt', 'Dublin', 'Nice'],
        'Frankfurt': ['Dublin', 'Krakow', 'Lyon', 'Nice']
    }
    
    # Days
    days = 20
    day_range = range(1, days + 1)
    
    # Create Z3 variables: for each day, which city are we in?
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in day_range]
    
    s = Solver()
    
    # Constraint: transitions must be via direct flights
    for d in range(2, days + 1):
        for c_idx, c in enumerate(cities):
            prev_day_same_city = day_city[d-2][c_idx]
            other_possible_prev_cities = []
            for c_prime_idx, c_prime in enumerate(cities):
                if c_prime != c and c in direct_flights[c_prime]:
                    other_possible_prev_cities.append(day_city[d-2][c_prime_idx])
            s.add(Implies(day_city[d-1][c_idx], Or(prev_day_same_city, *other_possible_prev_cities)))
    
    # Constraint: Nice between day 1-5 for 5 days
    nice_days = [day_city[d-1][city_to_idx['Nice']] for d in range(1, 6)]
    s.add(Sum([If(c, 1, 0) for c in nice_days]) == 5)
    
    # Constraint: Frankfurt between day 19-20 for 2 days
    frankfurt_days = [day_city[d-1][city_to_idx['Frankfurt']] for d in [19, 20]]
    s.add(Sum([If(c, 1, 0) for c in frankfurt_days]) == 2)
    
    # Total days per city
    s.add(Sum([If(day_city[d-1][city_to_idx['Nice']], 1, 0) for d in day_range]) == 5)
    s.add(Sum([If(day_city[d-1][city_to_idx['Krakow']], 1, 0) for d in day_range]) == 6)
    s.add(Sum([If(day_city[d-1][city_to_idx['Dublin']], 1, 0) for d in day_range]) == 7)
    s.add(Sum([If(day_city[d-1][city_to_idx['Lyon']], 1, 0) for d in day_range]) == 4)
    s.add(Sum([If(day_city[d-1][city_to_idx['Frankfurt']], 1, 0) for d in day_range]) == 2)
    
    # Ensure at least one city per day
    for d in day_range:
        s.add(Or([day_city[d-1][i] for i in range(len(cities))]))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in day_range:
            for c_idx, city in enumerate(cities):
                if model.evaluate(day_city[d-1][c_idx]):
                    itinerary.append({"day": d, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))