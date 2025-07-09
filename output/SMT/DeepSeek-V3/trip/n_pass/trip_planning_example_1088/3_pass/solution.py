from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
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
    
    # Direct flight connections (bidirectional)
    flight_connections = [
        ("Reykjavik", "Stuttgart"),
        ("Reykjavik", "Stockholm"),
        ("Reykjavik", "Tallinn"),
        ("Reykjavik", "Oslo"),
        ("Stockholm", "Oslo"),
        ("Stockholm", "Stuttgart"),
        ("Stockholm", "Split"),
        ("Stockholm", "Geneva"),
        ("Stuttgart", "Porto"),
        ("Stuttgart", "Split"),
        ("Oslo", "Split"),
        ("Oslo", "Geneva"),
        ("Oslo", "Porto"),
        ("Oslo", "Tallinn"),
        ("Geneva", "Porto"),
        ("Geneva", "Split"),
        ("Split", "Stuttgart")
    ]
    
    # Create city to ID mapping
    city_list = list(cities.keys())
    city_ids = {city: idx for idx, city in enumerate(city_list)}
    id_to_city = {idx: city for idx, city in enumerate(city_list)}
    
    # Create flight connection matrix
    connected = [[False]*len(cities) for _ in range(len(cities))]
    for src, dst in flight_connections:
        connected[city_ids[src]][city_ids[dst]] = True
        connected[city_ids[dst]][city_ids[src]] = True
    
    days = 21
    s = Solver()
    
    # day_place[d] = city ID for day d (1-based)
    day_place = [Int(f"day_{d}") for d in range(1, days+1)]
    
    # Each day must be assigned a valid city
    for d in range(days):
        s.add(day_place[d] >= 0, day_place[d] < len(cities))
    
    # Fixed constraints:
    # Reykjavik on days 1-2 (indices 0-1)
    s.add(day_place[0] == city_ids["Reykjavik"])
    s.add(day_place[1] == city_ids["Reykjavik"])
    
    # Porto between days 19-21 (indices 18-20)
    s.add(Or([day_place[d] == city_ids["Porto"] for d in range(18, 21)]))
    
    # Stockholm between days 2-4 (indices 1-3)
    s.add(Or([day_place[d] == city_ids["Stockholm"] for d in range(1, 4)]))
    
    # Flight constraints: consecutive different cities must be connected
    for d in range(days-1):
        current = day_place[d]
        next_ = day_place[d+1]
        s.add(Or(
            current == next_,
            *[And(current == i, next_ == j) 
              for i in range(len(cities)) 
              for j in range(len(cities)) 
              if connected[i][j]]
        ))
    
    # Total days per city must match requirements
    for city, req_days in cities.items():
        city_id = city_ids[city]
        total = Sum([If(day_place[d] == city_id, 1, 0) for d in range(days)])
        s.add(total == req_days)
    
    if s.check() == sat:
        m = s.model()
        # Build itinerary with flight days
        itinerary = []
        current_place = id_to_city[m.evaluate(day_place[0]).as_long()]
        start_day = 1
        
        for d in range(1, days):
            place = id_to_city[m.evaluate(day_place[d]).as_long()]
            if place != current_place:
                # Add stay up to previous day
                if start_day == d:
                    itinerary.append({"day_range": f"Day {d}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{d}", "place": current_place})
                # Add flight day (both cities)
                itinerary.append({"day_range": f"Day {d}", "place": current_place})
                itinerary.append({"day_range": f"Day {d}", "place": place})
                current_place = place
                start_day = d + 1
        
        # Add final stay
        if start_day <= days:
            if start_day == days:
                itinerary.append({"day_range": f"Day {days}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))