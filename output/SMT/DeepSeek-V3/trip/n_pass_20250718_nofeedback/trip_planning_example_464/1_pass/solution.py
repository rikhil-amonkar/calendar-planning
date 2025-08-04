from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency matrix
    direct_flights = [
        [False, True, True, False, False],   # Krakow
        [True, False, True, True, True],      # Frankfurt
        [True, True, False, True, True],      # Oslo
        [False, True, True, False, True],     # Dubrovnik
        [False, True, True, True, False]      # Naples
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day_place[d][c] is true if in city c on day d
    day_place = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in range(1, 19)]
    
    # Constraints
    
    # Each day, exactly one city is visited (including flight days)
    for day in range(18):
        day_vars = day_place[day]
        s.add(Or(day_vars))  # At least one city per day
        # No two cities on the same day
        for i in range(5):
            for j in range(i+1, 5):
                s.add(Or(Not(day_vars[i]), Not(day_vars[j])))
    
    # Transition constraints: if consecutive days are in different cities, there must be a direct flight
    for day in range(17):
        current_day = day_place[day]
        next_day = day_place[day + 1]
        for c1 in range(5):
            for c2 in range(5):
                if c1 != c2:
                    # If day is c1 and day+1 is c2, then there must be a direct flight
                    s.add(Implies(
                        And(current_day[c1], next_day[c2]),
                        direct_flights[c1][c2]
                    ))
    
    # Duration constraints
    # Krakow: 5 days
    krakow_days = [If(day_place[d][city_to_idx['Krakow']], 1, 0) for d in range(18)]
    s.add(sum(krakow_days) == 5)
    
    # Frankfurt: 4 days
    frankfurt_days = [If(day_place[d][city_to_idx['Frankfurt']], 1, 0) for d in range(18)]
    s.add(sum(frankfurt_days) == 4)
    
    # Oslo: 3 days, including days 16-18 (1-based, so indices 15-17)
    oslo_days = [If(day_place[d][city_to_idx['Oslo']], 1, 0) for d in range(18)]
    s.add(sum(oslo_days) == 3)
    # Days 16-18 (indices 15-17) must be Oslo
    for d in [15, 16, 17]:
        s.add(day_place[d][city_to_idx['Oslo']])
    
    # Dubrovnik: 5 days, with at least one day between 5-9 (indices 4-8)
    dubrovnik_days = [If(day_place[d][city_to_idx['Dubrovnik']], 1, 0) for d in range(18)]
    s.add(sum(dubrovnik_days) == 5)
    # At least one day between 5-9 (indices 4-8)
    s.add(Or([day_place[d][city_to_idx['Dubrovnik']] for d in range(4, 9)]))
    
    # Naples: 5 days
    naples_days = [If(day_place[d][city_to_idx['Naples']], 1, 0) for d in range(18)]
    s.add(sum(naples_days) == 5)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(18):
            for c in range(5):
                if m.evaluate(day_place[day][c]):
                    itinerary.append({"day": day + 1, "place": cities[c]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))