from z3 import *

def solve_itinerary():
    # Cities with required visit days
    cities = {
        "Mykonos": 4,
        "Krakow": 5,
        "Vilnius": 2,
        "Helsinki": 2,
        "Dubrovnik": 3,
        "Oslo": 2,
        "Madrid": 5,
        "Paris": 2
    }
    
    # Direct flight connections (bidirectional)
    flights = {
        "Oslo": ["Krakow", "Paris", "Madrid", "Helsinki", "Dubrovnik", "Vilnius"],
        "Krakow": ["Oslo", "Paris", "Vilnius", "Helsinki"],
        "Paris": ["Oslo", "Madrid", "Krakow", "Helsinki", "Vilnius"],
        "Helsinki": ["Vilnius", "Oslo", "Krakow", "Dubrovnik", "Paris", "Madrid"],
        "Vilnius": ["Helsinki", "Oslo", "Paris", "Krakow"],
        "Dubrovnik": ["Helsinki", "Madrid", "Oslo"],
        "Madrid": ["Paris", "Oslo", "Helsinki", "Dubrovnik", "Mykonos"],
        "Mykonos": ["Madrid"]
    }
    
    total_days = 18
    solver = Solver()
    
    # Day variables (1-based indexing)
    day_city = [Int(f"day_{d}") for d in range(1, total_days+1)]
    
    # City encodings
    city_list = sorted(cities.keys())
    city_id = {city: i for i, city in enumerate(city_list)}
    id_city = {i: city for i, city in enumerate(city_list)}
    
    # Each day must be assigned a valid city
    for d in range(total_days):
        solver.add(day_city[d] >= 0, day_city[d] < len(city_list))
    
    # Flight transitions between days
    for d in range(total_days-1):
        current = day_city[d]
        next_day = day_city[d+1]
        solver.add(Or(
            current == next_day,  # Stay in same city
            Or([And(current == city_id[src], next_day == city_id[dst])
               for src in flights for dst in flights[src]])
        ))
    
    # Fixed constraints
    # Oslo on day 1
    solver.add(day_city[0] == city_id["Oslo"])
    # Dubrovnik days 2-4 (indices 1-3)
    solver.add(day_city[1] == city_id["Dubrovnik"])
    solver.add(day_city[2] == city_id["Dubrovnik"])
    solver.add(day_city[3] == city_id["Dubrovnik"])
    # Mykonos days 15-18 (indices 14-17)
    solver.add(day_city[14] == city_id["Mykonos"])
    solver.add(day_city[15] == city_id["Mykonos"])
    solver.add(day_city[16] == city_id["Mykonos"])
    solver.add(day_city[17] == city_id["Mykonos"])
    
    # Total days per city
    for city, days in cities.items():
        solver.add(Sum([If(day_city[d] == city_id[city], 1, 0) 
                      for d in range(total_days)]) == days)
    
    # Solve and format itinerary
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current = None
        start = 1
        
        for d in range(total_days):
            city_idx = model.evaluate(day_city[d]).as_long()
            city = id_city[city_idx]
            
            if d == 0:
                current = city
                start = 1
            else:
                prev_idx = model.evaluate(day_city[d-1]).as_long()
                prev_city = id_city[prev_idx]
                
                if city != prev_city:
                    if start <= d:
                        itinerary.append({"day_range": f"Day {start}-{d+1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {d+1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {d+1}", "place": city})
                    start = d + 2
                    current = city
        
        if start <= total_days:
            itinerary.append({"day_range": f"Day {start}-{total_days}", "place": current})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))