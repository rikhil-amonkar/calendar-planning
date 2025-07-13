from z3 import *
import json

def solve_itinerary():
    cities = ["Paris", "Vienna", "Edinburgh", "Krakow", "Riga", "Hamburg", "Barcelona", "Stockholm"]
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Hamburg", "Stockholm"), ("Vienna", "Stockholm"), ("Paris", "Edinburgh"),
        ("Riga", "Barcelona"), ("Paris", "Riga"), ("Krakow", "Barcelona"),
        ("Edinburgh", "Stockholm"), ("Paris", "Krakow"), ("Krakow", "Stockholm"),
        ("Riga", "Edinburgh"), ("Barcelona", "Stockholm"), ("Paris", "Stockholm"),
        ("Krakow", "Edinburgh"), ("Vienna", "Hamburg"), ("Paris", "Hamburg"),
        ("Riga", "Stockholm"), ("Hamburg", "Barcelona"), ("Vienna", "Barcelona"),
        ("Krakow", "Vienna"), ("Riga", "Hamburg"), ("Barcelona", "Edinburgh"),
        ("Paris", "Barcelona"), ("Hamburg", "Edinburgh"), ("Paris", "Vienna"),
        ("Vienna", "Riga")
    ]
    
    # Create solver
    s = Solver()
    
    # Day variables (1-16)
    day_city = [Int(f"day_{i}") for i in range(1, 17)]
    for dc in day_city:
        s.add(dc >= 0, dc < 8)
    
    # Fixed events
    s.add(day_city[0] == city_to_int["Paris"])  # Day 1
    s.add(day_city[1] == city_to_int["Paris"])  # Day 2
    s.add(day_city[9] == city_to_int["Hamburg"])  # Day 10
    s.add(day_city[10] == city_to_int["Hamburg"])  # Day 11
    s.add(day_city[14] == city_to_int["Stockholm"])  # Day 15
    s.add(day_city[15] == city_to_int["Stockholm"])  # Day 16
    
    # Edinburgh visit between days 12-15
    s.add(Or([day_city[i] == city_to_int["Edinburgh"] for i in range(11, 15)]))
    
    # Flight connections
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((city_to_int[a], city_to_int[b]))
        flight_pairs.add((city_to_int[b], city_to_int[a]))
    
    for i in range(15):
        s.add(Or(
            day_city[i] == day_city[i+1],
            Or([And(day_city[i] == a, day_city[i+1] == b) for (a,b) in flight_pairs])
        ))
    
    # Duration constraints
    durations = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2
    }
    
    for city, days in durations.items():
        s.add(Sum([If(day_city[i] == city_to_int[city], 1, 0) for i in range(16)]) == days)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        schedule = [int_to_city[m.evaluate(day_city[i]).as_long()] for i in range(16)]
        
        # Build itinerary
        itinerary = []
        current = schedule[0]
        start = 1
        for day in range(1, 16):
            if schedule[day] != schedule[day-1]:
                if start < day:
                    itinerary.append({"day_range": f"Day {start}-{day}", "place": current})
                itinerary.append({"day_range": f"Day {day}", "place": current})
                itinerary.append({"day_range": f"Day {day}", "place": schedule[day]})
                current = schedule[day]
                start = day + 1
        if start <= 16:
            itinerary.append({"day_range": f"Day {start}-16", "place": current})
        
        return {"itinerary": itinerary}
    else:
        print("No valid itinerary exists with current constraints")
        return {"itinerary": []}

itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))