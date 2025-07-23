from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency matrix
    direct_flights = [
        [False, True, True, False, False],   # Krakow
        [True, False, True, True, True],    # Frankfurt
        [True, True, False, True, True],     # Oslo
        [False, True, True, False, True],    # Dubrovnik
        [False, True, True, True, False]    # Naples
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day_place[d] is the city index for day d (1-based)
    day_place = [Int(f"day_{day}") for day in range(1, 19)]
    for day in range(18):
        s.add(day_place[day] >= 0, day_place[day] < 5)
    
    # Transition constraints: if consecutive days are in different cities, there must be a direct flight
    for day in range(17):
        current_city = day_place[day]
        next_city = day_place[day + 1]
        s.add(Implies(current_city != next_city, 
                      direct_flights[current_city][next_city]))
    
    # Duration constraints
    # Krakow: 5 days
    s.add(Sum([If(day_place[day] == city_to_idx['Krakow'], 1, 0) for day in range(18)]) == 5)
    
    # Frankfurt: 4 days
    s.add(Sum([If(day_place[day] == city_to_idx['Frankfurt'], 1, 0) for day in range(18)]) == 4)
    
    # Oslo: 3 days, including days 16-18 (1-based, so indices 15-17)
    s.add(Sum([If(day_place[day] == city_to_idx['Oslo'], 1, 0) for day in range(18)]) == 3)
    s.add(day_place[15] == city_to_idx['Oslo'])
    s.add(day_place[16] == city_to_idx['Oslo'])
    s.add(day_place[17] == city_to_idx['Oslo'])
    
    # Dubrovnik: 5 days, with at least one day between 5-9 (indices 4-8)
    s.add(Sum([If(day_place[day] == city_to_idx['Dubrovnik'], 1, 0) for day in range(18)]) == 5)
    s.add(Or([day_place[day] == city_to_idx['Dubrovnik'] for day in range(4, 9)]))
    
    # Naples: 5 days
    s.add(Sum([If(day_place[day] == city_to_idx['Naples'], 1, 0) for day in range(18)]) == 5)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(18):
            city_idx = m.evaluate(day_place[day]).as_long()
            itinerary.append({"day": day + 1, "place": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))