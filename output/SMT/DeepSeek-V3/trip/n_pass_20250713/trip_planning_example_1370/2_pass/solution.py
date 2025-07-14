from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Paris", "Krakow"),
        ("Paris", "Amsterdam"),
        ("Paris", "Split"),
        ("Vilnius", "Munich"),
        ("Paris", "Geneva"),
        ("Amsterdam", "Geneva"),
        ("Munich", "Split"),
        ("Split", "Krakow"),
        ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"),
        ("Split", "Geneva"),
        ("Vilnius", "Split"),
        ("Munich", "Geneva"),
        ("Munich", "Krakow"),
        ("Krakow", "Vilnius"),
        ("Vilnius", "Amsterdam"),
        ("Budapest", "Paris"),
        ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"),
        ("Budapest", "Geneva"),
        ("Split", "Amsterdam"),
        ("Santorini", "Geneva"),
        ("Amsterdam", "Santorini"),
        ("Munich", "Budapest"),
        ("Munich", "Paris")
    ]
    
    # Make flight connections bidirectional
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Event constraints
    events = [
        ("Santorini", 25, 29),
        ("Krakow", 18, 22),
        ("Paris", 11, 15)
    ]
    
    # Total days
    total_days = 30
    
    # Create Z3 variables
    s = Solver()
    
    # day_place[i] is the city on day i+1
    city_names = list(cities.keys())
    day_place = [Int(f"day_{i+1}") for i in range(total_days)]
    for day in day_place:
        s.add(day >= 0, day < len(city_names))
    
    # Function to get city name from index
    def city_from_index(idx):
        return city_names[idx]
    
    # Flight transitions: if day i is city A and day i+1 is city B, then (A,B) must be in flight_pairs
    for i in range(total_days - 1):
        current_city = day_place[i]
        next_city = day_place[i + 1]
        s.add(Or([And(current_city == city_names.index(a), next_city == city_names.index(b)) for (a, b) in flight_pairs]))
    
    # Total days per city
    for city, days in cities.items():
        idx = city_names.index(city)
        s.add(Sum([If(day_place[i] == idx, 1, 0) for i in range(total_days)]) == days)
    
    # Event constraints: certain cities must be visited within specific day ranges
    for city, start_day, end_day in events:
        idx = city_names.index(city)
        s.add(Or([day_place[i] == idx for i in range(start_day - 1, end_day)]))
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        itinerary = []
        current_city = None
        start_day = 1
        for day in range(total_days):
            city_idx = m.evaluate(day_place[day]).as_long()
            city = city_names[city_idx]
            if day == 0:
                start_day = 1
                current_city = city
            else:
                prev_city_idx = m.evaluate(day_place[day - 1]).as_long()
                prev_city = city_names[prev_city_idx]
                if city == prev_city:
                    pass
                else:
                    # End previous city's stay
                    if start_day == day:
                        itinerary.append({"day_range": f"Day {day}", "place": prev_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day}", "place": prev_city})
                    # Flight day: day is in both cities
                    itinerary.append({"day_range": f"Day {day + 1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day + 1}", "place": city})
                    start_day = day + 2
                    current_city = city
        # Add the last city's stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {total_days}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        # Post-process to merge consecutive days in the same city
        merged_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            current = itinerary[i]
            if i < n - 1 and itinerary[i+1]["place"] == current["place"]:
                start = int(current["day_range"].split('-')[0].replace("Day ", ""))
                j = i + 1
                while j < n and itinerary[j]["place"] == current["place"]:
                    j += 1
                end = int(itinerary[j-1]["day_range"].split('-')[-1].replace("Day ", ""))
                merged_range = f"Day {start}-{end}"
                merged_itinerary.append({"day_range": merged_range, "place": current["place"]})
                i = j
            else:
                merged_itinerary.append(current)
                i += 1
        
        return {"itinerary": merged_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))