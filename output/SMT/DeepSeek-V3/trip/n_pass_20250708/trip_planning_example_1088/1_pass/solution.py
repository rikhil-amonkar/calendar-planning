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
        "Stuttgart": ["Porto", "Stockholm", "Split", "Reykjavik"],
        "Oslo": ["Stockholm", "Split", "Geneva", "Porto", "Tallinn", "Reykjavik"],
        "Split": ["Stuttgart", "Oslo", "Geneva", "Stockholm"],
        "Geneva": ["Oslo", "Porto", "Split", "Stockholm"],
        "Porto": ["Stuttgart", "Oslo", "Geneva"],
        "Tallinn": ["Oslo", "Reykjavik"]
    }
    
    # Create city to ID mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    days = 21
    s = Solver()
    
    # day_place[d] represents the city on day d (1-based)
    day_place = [Int(f"day_{d}") for d in range(1, days + 1)]
    
    # Each day's place must be a valid city ID
    for d in range(days):
        s.add(day_place[d] >= 0, day_place[d] < len(cities))
    
    # Fixed constraints:
    # Reykjavik on days 1 and 2 (indices 0 and 1)
    s.add(day_place[0] == city_ids["Reykjavik"])
    s.add(day_place[1] == city_ids["Reykjavik"])
    
    # Porto on days 19-21 (indices 18-20)
    s.add(Or([day_place[d] == city_ids["Porto"] for d in range(18, 21)]))
    
    # Stockholm between days 2-4 (indices 1-3)
    s.add(Or([day_place[d] == city_ids["Stockholm"] for d in range(1, 4)]))
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for d in range(days - 1):
        current_city = day_place[d]
        next_city = day_place[d + 1]
        # Either same city or connected by flight
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[src], next_city == city_ids[dst])
              for src in direct_flights for dst in direct_flights[src]
        ))
    
    # Total days per city
    for city, required_days in cities.items():
        city_id = city_ids[city]
        total_days = Sum([If(day_place[d] == city_id, 1, 0) for d in range(days)])
        s.add(total_days == required_days)
    
    if s.check() == sat:
        m = s.model()
        # Extract the day assignments
        day_assignments = []
        for d in range(days):
            city_id = m.evaluate(day_place[d]).as_long()
            day_assignments.append(id_to_city[city_id])
        
        # Build the itinerary
        itinerary = []
        current_place = day_assignments[0]
        start_day = 1
        
        for d in range(1, days):
            if day_assignments[d] != current_place:
                # Add the stay up to d
                if start_day == d:
                    day_str = f"Day {d}"
                else:
                    day_str = f"Day {start_day}-{d}"
                itinerary.append({"day_range": day_str, "place": current_place})
                # Add the flight day (day d) for both cities
                itinerary.append({"day_range": f"Day {d}", "place": current_place})
                itinerary.append({"day_range": f"Day {d}", "place": day_assignments[d]})
                current_place = day_assignments[d]
                start_day = d + 1
        # Add the last stay
        if start_day <= days:
            if start_day == days:
                day_str = f"Day {days}"
            else:
                day_str = f"Day {start_day}-{days}"
            itinerary.append({"day_range": day_str, "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))