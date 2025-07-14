from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["Paris", "Vienna", "Edinburgh", "Krakow", "Riga", "Hamburg", "Barcelona", "Stockholm"]
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Hamburg", "Stockholm"),
        ("Vienna", "Stockholm"),
        ("Paris", "Edinburgh"),
        ("Riga", "Barcelona"),
        ("Paris", "Riga"),
        ("Krakow", "Barcelona"),
        ("Edinburgh", "Stockholm"),
        ("Paris", "Krakow"),
        ("Krakow", "Stockholm"),
        ("Riga", "Edinburgh"),
        ("Barcelona", "Stockholm"),
        ("Paris", "Stockholm"),
        ("Krakow", "Edinburgh"),
        ("Vienna", "Hamburg"),
        ("Paris", "Hamburg"),
        ("Riga", "Stockholm"),
        ("Hamburg", "Barcelona"),
        ("Vienna", "Barcelona"),
        ("Krakow", "Vienna"),
        ("Riga", "Hamburg"),
        ("Barcelona", "Edinburgh"),
        ("Paris", "Barcelona"),
        ("Hamburg", "Edinburgh"),
        ("Paris", "Vienna"),
        ("Vienna", "Riga")
    ]
    
    # Create a set of direct flight pairs for easy lookup
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    s = Solver()
    
    # Variables: for each day (1..16), which city are we in?
    day_city = [Int(f"day_{i}") for i in range(1, 17)]
    for dc in day_city:
        s.add(dc >= 0, dc < 8)
    
    # Constraints for specific events:
    # Paris: wedding on day 1-2
    s.add(day_city[0] == city_to_int["Paris"])
    s.add(day_city[1] == city_to_int["Paris"])
    
    # Hamburg: conference on day 10-11 (indices 9-10)
    s.add(day_city[9] == city_to_int["Hamburg"])
    s.add(day_city[10] == city_to_int["Hamburg"])
    
    # Edinburgh: meet friend between day 12-15 (indices 11-14)
    s.add(Or([day_city[i] == city_to_int["Edinburgh"] for i in range(11, 15)]))
    
    # Stockholm: relatives between day 15-16 (indices 14-15)
    s.add(day_city[14] == city_to_int["Stockholm"])
    s.add(day_city[15] == city_to_int["Stockholm"])
    
    # Flight transitions: consecutive days must be either same city or direct flight
    for i in range(15):
        current = day_city[i]
        next_ = day_city[i+1]
        s.add(Or(
            current == next_,
            Or([And(current == city_to_int[a], next_ == city_to_int[b]) for a, b in flight_pairs if a in city_to_int and b in city_to_int])
        ))
    
    # Duration constraints:
    # Vienna: 4 days
    s.add(Sum([If(day_city[i] == city_to_int["Vienna"], 1, 0) for i in range(16)]) == 4)
    # Barcelona: 2 days
    s.add(Sum([If(day_city[i] == city_to_int["Barcelona"], 1, 0) for i in range(16)]) == 2)
    # Edinburgh: 4 days
    s.add(Sum([If(day_city[i] == city_to_int["Edinburgh"], 1, 0) for i in range(16)]) == 4)
    # Krakow: 3 days
    s.add(Sum([If(day_city[i] == city_to_int["Krakow"], 1, 0) for i in range(16)]) == 3)
    # Riga: 4 days
    s.add(Sum([If(day_city[i] == city_to_int["Riga"], 1, 0) for i in range(16)]) == 4)
    # Hamburg: 2 days (already constrained days 10-11)
    s.add(Sum([If(day_city[i] == city_to_int["Hamburg"], 1, 0) for i in range(16)]) == 2)
    # Paris: 2 days (already constrained days 1-2)
    s.add(Sum([If(day_city[i] == city_to_int["Paris"], 1, 0) for i in range(16)]) == 2)
    # Stockholm: 2 days (already constrained days 15-16)
    s.add(Sum([If(day_city[i] == city_to_int["Stockholm"], 1, 0) for i in range(16)]) == 2)
    
    if s.check() == sat:
        m = s.model()
        # Extract the city for each day
        schedule = []
        for day in range(1, 17):
            city_idx = m.evaluate(day_city[day-1]).as_long()
            schedule.append(int_to_city[city_idx])
        
        # Build the itinerary with day ranges and flight days
        itinerary = []
        current_city = schedule[0]
        start_day = 1
        for day in range(2, 17):
            if schedule[day-1] != schedule[day-2]:
                # Flight day
                if start_day < day:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day-1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day-1}", "place": schedule[day-1]})
                current_city = schedule[day-1]
                start_day = day
        # Add the last stretch
        if start_day <= 16:
            itinerary.append({"day_range": f"Day {start_day}-16", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Generate the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))