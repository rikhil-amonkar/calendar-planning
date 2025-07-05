from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5
    }
    
    # Direct flights (as a set of tuples)
    direct_flights = set([
        ("Oslo", "Stockholm"),
        ("Krakow", "Frankfurt"),
        ("Krakow", "Istanbul"),
        ("Munich", "Stockholm"),
        ("Hamburg", "Stockholm"),
        ("Krakow", "Vilnius"),
        ("Oslo", "Istanbul"),
        ("Istanbul", "Stockholm"),
        ("Oslo", "Krakow"),
        ("Vilnius", "Istanbul"),
        ("Oslo", "Vilnius"),
        ("Frankfurt", "Istanbul"),
        ("Oslo", "Frankfurt"),
        ("Munich", "Hamburg"),
        ("Munich", "Istanbul"),
        ("Oslo", "Munich"),
        ("Frankfurt", "Florence"),
        ("Oslo", "Hamburg"),
        ("Vilnius", "Frankfurt"),
        ("Florence", "Munich"),
        ("Krakow", "Munich"),
        ("Hamburg", "Istanbul"),
        ("Frankfurt", "Stockholm"),
        ("Stockholm", "Santorini"),
        ("Frankfurt", "Munich"),
        ("Santorini", "Oslo"),
        ("Krakow", "Stockholm"),
        ("Vilnius", "Munich"),
        ("Frankfurt", "Hamburg")
    ])
    
    # Make flights bidirectional
    flights = set()
    for a, b in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    
    # Fixed periods
    fixed_periods = [
        ("Istanbul", 25, 29),
        ("Krakow", 5, 9)
    ]
    
    # Create solver with a timeout
    s = Solver()
    s.set("timeout", 10000)  # 10 seconds timeout
    
    # Variables: assign each day to a city
    days = 32
    city_names = list(cities.keys())
    city_vars = [Int(f"day_{i}") for i in range(1, days + 1)]
    for var in city_vars:
        s.add(var >= 0, var < len(city_names))
    
    # Assign fixed periods
    for city, start, end in fixed_periods:
        city_idx = city_names.index(city)
        for day in range(start, end + 1):
            s.add(city_vars[day - 1] == city_idx)
    
    # Duration constraints
    for city, req_days in cities.items():
        city_idx = city_names.index(city)
        s.add(Sum([If(city_vars[i] == city_idx, 1, 0) for i in range(days)]) == req_days)
    
    # Flight constraints: consecutive days must be same city or connected by flight
    for i in range(days - 1):
        current_city = city_vars[i]
        next_city = city_vars[i + 1]
        same_city = current_city == next_city
        flight_exists = Or([And(current_city == city_names.index(a), next_city == city_names.index(b))
                          for a, b in flights])
        s.add(Or(same_city, flight_exists))
    
    # Check and model
    if s.check() == sat:
        m = s.model()
        # Extract the day assignments
        day_assignments = []
        for i in range(days):
            day = i + 1
            city_idx = m.evaluate(city_vars[i]).as_long()
            city = city_names[city_idx]
            day_assignments.append((day, city))
        
        # Generate itinerary with flight days
        itinerary = []
        current_place = day_assignments[0][1]
        start_day = 1
        for day, place in day_assignments[1:]:
            if place == current_place:
                continue
            else:
                end_day = day - 1
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                # Flight day
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": place})
                current_place = place
                start_day = day
        # Add the last stay
        if start_day <= days:
            if start_day == days:
                itinerary.append({"day_range": f"Day {days}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found within the time limit"}

itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))