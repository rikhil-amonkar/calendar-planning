from z3 import *
import json

def solve_trip_planning():
    # Cities and their required days
    cities = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos")
    ]
    
    # Correcting city names in flights
    corrected_flights = []
    for a, b in direct_flights:
        if a == "Helsinki":
            a = "Helsinki"
        if b == "Helsinki":
            b = "Helsinki"
        if a == "Madrid":
            a = "Madrid"
        if b == "Madrid":
            b = "Madrid"
        corrected_flights.append((a, b))
    
    flight_pairs = set()
    for a, b in corrected_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    total_days = 21
    
    city_names = sorted(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_names)}
    int_to_city = {idx: city for idx, city in enumerate(city_names)}
    
    s = Solver()
    
    day_city = [Int(f"day_{i}") for i in range(total_days)]
    
    for day in range(total_days):
        s.add(day_city[day] >= 0, day_city[day] < len(city_names))
    
    for day in range(total_days - 1):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        s.add(Implies(current_city != next_city,
                      Or([And(current_city == city_to_int[a], next_city == city_to_int[b])
                          for a, b in flight_pairs])))
    
    for city, days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day_city[i] == city_idx, 1, 0) for i in range(total_days)]) == days)
    
    s.add(day_city[19] == city_to_int["Madrid"])  # Day 20
    s.add(day_city[20] == city_to_int["Madrid"])  # Day 21
    
    stuttgart_idx = city_to_int["Stuttgart"]
    s.add(Or([day_city[i] == stuttgart_idx for i in range(4)]))  # Days 1-4
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1  # 1-based
        
        for day in range(total_days):
            city_idx = model.evaluate(day_city[day]).as_long()
            city = int_to_city[city_idx]
            
            if current_city is None:
                current_city = city
                start_day = day + 1
            elif city == current_city:
                continue
            else:
                if start_day == day + 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day + 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day + 1}", "place": city})
                current_city = city
                start_day = day + 1
        
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_trip_planning()
print(json.dumps(result, indent=2))