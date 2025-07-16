from z3 import *
import json

def solve_itinerary():
    cities = {
        "Oslo": 5,
        "Stuttgart": 5,
        "Reykjavik": 2,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3
    }
    
    direct_flights = {
        "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
        "Stockholm": ["Oslo", "Stuttgart", "Split", "Geneva", "Reykjavik"],
        "Stuttgart": ["Porto", "Stockholm", "Split"],
        "Oslo": ["Split", "Geneva", "Porto", "Stockholm", "Tallinn", "Reykjavik"],
        "Split": ["Stuttgart", "Oslo", "Geneva", "Stockholm"],
        "Geneva": ["Porto", "Split", "Oslo", "Stockholm"],
        "Porto": ["Stuttgart", "Geneva", "Oslo"],
        "Tallinn": ["Oslo", "Reykjavik"]
    }
    
    total_days = 21
    days = range(1, total_days + 1)
    
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    day_vars = [Int(f"day_{i}") for i in days]
    
    for d in day_vars:
        s.add(d >= 0, d < len(cities))
    
    # Reykjavik on days 1 and 2
    s.add(day_vars[0] == city_ids["Reykjavik"])
    s.add(day_vars[1] == city_ids["Reykjavik"])
    
    # Porto on days 19-21 (indices 18-20)
    s.add(day_vars[18] == city_ids["Porto"])
    s.add(day_vars[19] == city_ids["Porto"])
    s.add(day_vars[20] == city_ids["Porto"])
    
    # Stockholm between day 2 and 4 (indices 1-3)
    s.add(Or(
        day_vars[1] == city_ids["Stockholm"],
        day_vars[2] == city_ids["Stockholm"],
        day_vars[3] == city_ids["Stockholm"]
    ))
    
    # Flight transitions: for each consecutive day, either stay or move to a directly connected city
    for i in range(total_days - 1):
        current = day_vars[i]
        next_ = day_vars[i + 1]
        # Create a condition that next city is either the same or a direct flight
        conditions = [current == next_]
        for city in direct_flights:
            src_id = city_ids[city]
            for dest in direct_flights[city]:
                dest_id = city_ids[dest]
                conditions.append(And(current == src_id, next_ == dest_id))
        s.add(Or(*conditions))
    
    # Duration constraints
    for city, days_required in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day_vars[i] == city_id, 1, 0) for i in range(total_days)]) == days_required)
    
    if s.check() == sat:
        model = s.model()
        day_sequence = [id_to_city[model.evaluate(day_vars[i]).as_long()] for i in range(total_days)]
        
        itinerary = []
        current_place = day_sequence[0]
        start_day = 1
        
        for day in range(1, total_days):
            if day_sequence[day] != current_place:
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_place})
                itinerary.append({"day_range": f"Day {day + 1}", "place": day_sequence[day]})
                current_place = day_sequence[day]
                start_day = day + 1
        
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))