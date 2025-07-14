import json
from z3 import *

def solve_trip_planning():
    # Cities and their required days
    cities = {
        "Lyon": 3,
        "Paris": 5,
        "Riga": 2,
        "Berlin": 2,
        "Stockholm": 3,
        "Zurich": 5,
        "Nice": 2,
        "Seville": 3,
        "Milan": 3,
        "Naples": 4
    }
    
    # Direct flights as adjacency list
    flights = {
        "Paris": ["Stockholm", "Seville", "Zurich", "Nice", "Lyon", "Riga", "Naples"],
        "Stockholm": ["Paris", "Berlin", "Riga", "Zurich", "Nice", "Milan"],
        "Seville": ["Paris", "Milan"],
        "Naples": ["Zurich", "Milan", "Berlin", "Paris", "Nice"],
        "Nice": ["Riga", "Paris", "Zurich", "Stockholm", "Naples", "Lyon"],
        "Berlin": ["Milan", "Stockholm", "Naples", "Zurich", "Riga", "Paris", "Nice"],
        "Riga": ["Nice", "Milan", "Paris", "Stockholm", "Zurich", "Berlin"],
        "Zurich": ["Naples", "Paris", "Nice", "Milan", "Stockholm", "Riga", "Berlin"],
        "Lyon": ["Paris", "Nice"],
        "Milan": ["Berlin", "Paris", "Naples", "Riga", "Zurich", "Stockholm", "Seville"]
    }
    
    # Fixed events
    # Wedding in Berlin between day 1 and 2 (so days 1 and 2 are Berlin)
    # Workshop in Nice between day 12 and 13 (so days 12 and 13 are Nice)
    # Stockholm show from day 20 to 22 (so days 20,21,22 are Stockholm)
    
    total_days = 23
    Day = [Int(f'Day_{i}') for i in range(1, total_days + 1)]
    
    s = Solver()
    
    # Each day's city must be one of the 10 cities
    city_names = list(cities.keys())
    city_map = {city: idx for idx, city in enumerate(city_names)}
    for day in Day:
        s.add(Or([day == city_map[city] for city in city_names]))
    
    # Fixed events
    s.add(Day[0] == city_map["Berlin"])  # Day 1
    s.add(Day[1] == city_map["Berlin"])  # Day 2
    s.add(Day[11] == city_map["Nice"])   # Day 12
    s.add(Day[12] == city_map["Nice"])   # Day 13
    for i in range(19, 22):  # Days 20,21,22
        s.add(Day[i] == city_map["Stockholm"])
    
    # Flight constraints: consecutive days must be connected by a direct flight or stay in the same city
    for i in range(total_days - 1):
        current_city = Day[i]
        next_city = Day[i+1]
        s.add(Or(
            current_city == next_city,
            And([next_city == city_map[city] for city in flights[city_names[model[current_city].as_long()]]])
        ))
    
    # Total days per city
    for city in cities:
        total = 0
        for day in Day:
            total += If(day == city_map[city], 1, 0)
        s.add(total == cities[city])
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Process each day to build the itinerary
        current_place = None
        start_day = 1
        for day_num in range(1, total_days + 1):
            day_var = Day[day_num - 1]
            place = city_names[model[day_var].as_long()]
            
            if day_num == 1:
                current_place = place
                start_day = 1
            else:
                prev_place = city_names[model[Day[day_num - 2]].as_long()]
                if place != prev_place:
                    # Flight day: add previous stay and flight entries
                    if start_day != day_num - 1:
                        itinerary.append({
                            "day_range": f"Day {start_day}-{day_num - 1}",
                            "place": prev_place
                        })
                    else:
                        itinerary.append({
                            "day_range": f"Day {start_day}",
                            "place": prev_place
                        })
                    # Add flight entries (both departure and arrival)
                    itinerary.append({
                        "day_range": f"Day {day_num}",
                        "place": prev_place
                    })
                    itinerary.append({
                        "day_range": f"Day {day_num}",
                        "place": place
                    })
                    current_place = place
                    start_day = day_num
                else:
                    continue
        
        # Add the last stay
        if start_day == total_days:
            itinerary.append({
                "day_range": f"Day {start_day}",
                "place": current_place
            })
        else:
            itinerary.append({
                "day_range": f"Day {start_day}-{total_days}",
                "place": current_place
            })
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_trip_planning()
print(json.dumps(result, indent=2))