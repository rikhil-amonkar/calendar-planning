from z3 import *
import json

def solve_itinerary():
    cities = ['Mykonos', 'Nice', 'Prague', 'Zurich', 'Bucharest', 'Valencia', 'Riga']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    flights = {
        'Mykonos': ['Nice', 'Zurich'],
        'Nice': ['Mykonos', 'Riga', 'Zurich'],
        'Prague': ['Bucharest', 'Zurich', 'Riga', 'Valencia'],
        'Zurich': ['Mykonos', 'Nice', 'Prague', 'Bucharest', 'Valencia', 'Riga'],
        'Bucharest': ['Prague', 'Valencia', 'Zurich', 'Riga'],
        'Valencia': ['Bucharest', 'Zurich', 'Prague'],
        'Riga': ['Nice', 'Zurich', 'Bucharest', 'Prague']
    }
    
    required_days = {
        'Mykonos': 3,
        'Nice': 2,
        'Prague': 3,
        'Zurich': 5,
        'Bucharest': 5,
        'Valencia': 5,
        'Riga': 5
    }
    
    fixed_placements = [
        (1, 3, 'Mykonos'),
        (7, 9, 'Prague')
    ]
    
    total_days = 22
    s = Solver()
    
    day_place = [[Bool(f"day_{i+1}_city_{c}") for c in cities] for i in range(total_days)]
    
    # Each day is in at least one city
    for i in range(total_days):
        s.add(Or(day_place[i]))
    
    # If a day is in two cities, they must be connected by a flight
    for i in range(total_days):
        for c1 in range(len(cities)):
            for c2 in range(c1 + 1, len(cities)):
                city1 = cities[c1]
                city2 = cities[c2]
                s.add(Implies(And(day_place[i][c1], day_place[i][c2]),
                             Or(city2 in flights[city1], city1 in flights[city2])))
    
    # Fixed placements
    for start, end, city in fixed_placements:
        c_idx = city_indices[city]
        for day in range(start, end + 1):
            s.add(day_place[day - 1][c_idx])
    
    # Total days per city
    for city in cities:
        c_idx = city_indices[city]
        total = 0
        for i in range(total_days):
            total += If(day_place[i][c_idx], 1, 0)
        s.add(total == required_days[city])
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Determine for each day which cities are visited
        day_to_cities = []
        for i in range(total_days):
            day = i + 1
            active = []
            for c_idx in range(len(cities)):
                if m.evaluate(day_place[i][c_idx]):
                    active.append(cities[c_idx])
            day_to_cities.append((day, active))
        
        # Build the itinerary
        i = 0
        while i < total_days:
            day, active_cities = day_to_cities[i]
            if len(active_cities) == 1:
                city = active_cities[0]
                start_day = day
                j = i + 1
                while j < total_days and len(day_to_cities[j][1]) == 1 and day_to_cities[j][1][0] == city:
                    j += 1
                end_day = day + (j - i) - 1
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                # If this stay ends with a flight on end_day, we need to add individual entries
                if j < total_days and len(day_to_cities[j][1]) == 2:
                    # The end_day is a flight day
                    itinerary.append({"day_range": f"Day {end_day}", "place": city})
                i = j
            else:
                city1, city2 = active_cities
                itinerary.append({"day_range": f"Day {day}", "place": city1})
                itinerary.append({"day_range": f"Day {day}", "place": city2})
                i += 1
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))