import json
from z3 import *

def solve_trip_plan():
    cities = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4
    }
    
    direct_flights = [
        ("Vienna", "Bucharest"),
        ("Santorini", "Madrid"),
        ("Seville", "Valencia"),
        ("Vienna", "Seville"),
        ("Madrid", "Valencia"),
        ("Bucharest", "Riga"),
        ("Valencia", "Bucharest"),
        ("Santorini", "Bucharest"),
        ("Vienna", "Valencia"),
        ("Vienna", "Madrid"),
        ("Valencia", "Krakow"),
        ("Valencia", "Frankfurt"),
        ("Krakow", "Frankfurt"),
        ("Riga", "Tallinn"),
        ("Vienna", "Krakow"),
        ("Vienna", "Frankfurt"),
        ("Madrid", "Seville"),
        ("Santorini", "Vienna"),
        ("Vienna", "Riga"),
        ("Frankfurt", "Tallinn"),
        ("Frankfurt", "Bucharest"),
        ("Madrid", "Bucharest"),
        ("Frankfurt", "Riga"),
        ("Madrid", "Frankfurt")
    ]
    
    all_cities = list(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(all_cities)}
    
    solver = Solver()
    day_to_city = [Int(f"day_{day}") for day in range(1, 28)]
    
    for day in range(1, 28):
        solver.add(day_to_city[day - 1] >= 0, day_to_city[day - 1] < len(all_cities))
    
    # Fixed events
    for day in [3, 4, 5, 6]:
        solver.add(day_to_city[day - 1] == city_to_int["Vienna"])
    for day in [20, 21, 22, 23]:
        solver.add(day_to_city[day - 1] == city_to_int["Riga"])
    for day in [23, 24, 25, 26, 27]:
        solver.add(day_to_city[day - 1] == city_to_int["Tallinn"])
    solver.add(day_to_city[6] == city_to_int["Madrid"])
    solver.add(day_to_city[7] == city_to_int["Madrid"])
    for day in [11, 12, 13, 14, 15]:
        solver.add(day_to_city[day - 1] == city_to_int["Krakow"])
    
    for city in all_cities:
        required_days = cities[city]
        solver.add(Sum([If(day_to_city[day - 1] == city_to_int[city], 1, 0) for day in range(1, 28)]) == required_days)
    
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    for day in range(1, 27):
        current_city = day_to_city[day - 1]
        next_city = day_to_city[day]
        solver.add(Or([And(current_city == city_to_int[a], next_city == city_to_int[b]) for a, b in flight_pairs]))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary_days = []
        for day in range(1, 28):
            city_idx = model.evaluate(day_to_city[day - 1]).as_long()
            city = all_cities[city_idx]
            itinerary_days.append((day, city))
        
        itinerary = []
        current_place = itinerary_days[0][1]
        start_day = 1
        for day in range(2, 28):
            if itinerary_days[day - 1][1] != current_place:
                end_day_prev_segment = day - 1
                if start_day == end_day_prev_segment:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day_prev_segment}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                new_place = itinerary_days[day - 1][1]
                itinerary.append({"day_range": f"Day {day}", "place": new_place})
                current_place = new_place
                start_day = day
        if start_day <= 27:
            if start_day == 27:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-27", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_trip_plan()
print(json.dumps(result, indent=2))