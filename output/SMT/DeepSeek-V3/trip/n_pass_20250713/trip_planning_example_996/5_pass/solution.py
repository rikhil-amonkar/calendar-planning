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
        (1, 3, 'Mykonos'),  # Wedding in Mykonos days 1-3
        (7, 9, 'Prague')    # Relatives in Prague days 7-9
    ]
    
    total_days = 22
    s = Solver()
    
    # Variables: city for each day (None for flight days)
    day_city = [Int(f'day_{i+1}') for i in range(total_days)]
    for dc in day_city:
        s.add(dc >= 0, dc < len(cities))
    
    # Flight variables: is day i a flight day?
    is_flight = [Bool(f'flight_{i+1}') for i in range(total_days)]
    
    # Flight constraints
    for i in range(total_days):
        # If it's a flight day, next day must be different city
        if i < total_days - 1:
            s.add(Implies(is_flight[i], day_city[i] != day_city[i+1]))
        # Flight days must be between connected cities
        if i > 0 and i < total_days - 1:
            s.add(Implies(is_flight[i], 
                         Or([And(day_city[i-1] == city_indices[c1], 
                                day_city[i+1] == city_indices[c2], 
                                c2 in flights[c1])
                            for c1 in cities for c2 in flights[c1]])))
    
    # Fixed placements
    for start, end, city in fixed_placements:
        c_idx = city_indices[city]
        for day in range(start-1, end):
            s.add(day_city[day] == c_idx)
            s.add(Not(is_flight[day]))  # No flights during fixed stays
    
    # Required days per city
    for city, days in required_days.items():
        c_idx = city_indices[city]
        s.add(Sum([If(day_city[i] == c_idx, 1, 0) for i in range(total_days)]) == days)
    
    # Continuity constraints
    for i in range(total_days - 1):
        # Either same city or flight between them
        s.add(Or(day_city[i] == day_city[i+1],
                 is_flight[i]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Build day assignments
        assignments = []
        for i in range(total_days):
            city_idx = m.evaluate(day_city[i]).as_long()
            flight = m.evaluate(is_flight[i])
            assignments.append((i+1, cities[city_idx], flight))
        
        # Group consecutive days in same city
        current_city = assignments[0][1]
        start_day = 1
        for day in range(2, total_days + 1):
            if assignments[day-1][1] != current_city or assignments[day-2][2]:
                end_day = day - 1
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
                if assignments[day-2][2]:  # If previous day was flight
                    itinerary.append({"day_range": f"Day {end_day}", "place": assignments[day-2][1]})
                    itinerary.append({"day_range": f"Day {end_day}", "place": assignments[day-1][1]})
                start_day = day
                current_city = assignments[day-1][1]
        # Add last segment
        itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        # Verify all constraints are met
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            if "-" in entry["day_range"]:
                start, end = map(int, entry["day_range"].split("-")[0][4:].split("-"))
                day_counts[entry["place"]] += end - start + 1
            else:
                day_counts[entry["place"]] += 1
        
        for city, days in required_days.items():
            if day_counts[city] != days:
                return {"error": f"Day count mismatch for {city}"}
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))