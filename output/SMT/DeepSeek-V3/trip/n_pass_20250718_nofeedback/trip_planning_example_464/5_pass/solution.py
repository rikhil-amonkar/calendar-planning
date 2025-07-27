from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights adjacency matrix
    flights = [
        [False, True,  True,  False, False],  # Krakow
        [True,  False, True,  True,  True],   # Frankfurt
        [True,  True,  False, True,  True],   # Oslo
        [False, True,  True,  False, True],   # Dubrovnik
        [False, True,  True,  True,  False]   # Naples
    ]
    
    s = Solver()
    
    # Decision variables: city for each day (1-18)
    day_city = [Int(f'day_{d}_city') for d in range(1, 19)]
    for d in range(18):
        s.add(day_city[d] >= 0, day_city[d] < 5)
    
    # Flight constraints between consecutive days
    for d in range(17):
        current = day_city[d]
        next_day = day_city[d+1]
        # If changing cities, must have direct flight
        s.add(Implies(current != next_day, 
                     Or([And(current == i, next_day == j) 
                        for i in range(5) for j in range(5) if flights[i][j]])))
    
    # Duration constraints (each day counts for its city)
    s.add(Sum([If(day_city[d] == city_idx['Krakow'], 1, 0) for d in range(18)]) == 5)
    s.add(Sum([If(day_city[d] == city_idx['Frankfurt'], 1, 0) for d in range(18)]) == 4)
    s.add(Sum([If(day_city[d] == city_idx['Oslo'], 1, 0) for d in range(18)]) == 3)
    s.add(Sum([If(day_city[d] == city_idx['Dubrovnik'], 1, 0) for d in range(18)]) == 5)
    s.add(Sum([If(day_city[d] == city_idx['Naples'], 1, 0) for d in range(18)]) == 5)
    
    # Specific date constraints
    # Oslo must be days 16-18 (indices 15-17)
    s.add(day_city[15] == city_idx['Oslo'])
    s.add(day_city[16] == city_idx['Oslo'])
    s.add(day_city[17] == city_idx['Oslo'])
    
    # Dubrovnik must include at least one day between 5-9 (indices 4-8)
    s.add(Or([day_city[d] == city_idx['Dubrovnik'] for d in range(4, 9)]))
    
    # Solve and return itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(18):
            city = cities[m.evaluate(day_city[d]).as_long()]
            itinerary.append({"day": d+1, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

import json
print(json.dumps(solve_itinerary(), indent=2))