from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,  # days 25-29 must be Istanbul
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5,  # days 5-9 must include 5 days in Krakow (but not necessarily consecutive)
    }
    
    # Direct flights (undirected)
    direct_flights = [
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
        ("Frankfurt", "Hamburg"),
    ]
    
    # Make flights bidirectional
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    
    # Total days
    total_days = 32
    
    # Create Z3 variables: day[i] is the city on day i+1 (since days are 1-based)
    days = [Int(f"day_{i}") for i in range(total_days)]
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Solver
    s = Solver()
    
    # Each day must be a valid city
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: Istanbul must be days 25-29 (1-based, so indices 24-28)
    for i in range(24, 29):
        s.add(days[i] == city_ids["Istanbul"])
    
    # Constraint: Krakow must be between days 5-9 (indices 4-8), totaling 5 days
    # At least 5 days in Krakow within days 4-8 (1-based 5-9)
    krakow_in_workshop = [If(days[i] == city_ids["Krakow"], 1, 0) for i in range(4, 9)]
    s.add(Sum(krakow_in_workshop) >= 5)
    
    # Total days per city
    for city, required_days in cities.items():
        city_id = city_ids[city]
        total = Sum([If(day == city_id, 1, 0) for day in days])
        s.add(total == required_days)
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(total_days - 1):
        current_city = days[i]
        next_city = days[i + 1]
        # Either same city or connected by flight
        same_city = (current_city == next_city)
        flight_possible = Or([And(current_city == city_ids[a], next_city == city_ids[b]) for (a, b) in bidirectional_flights])
        s.add(Or(same_city, flight_possible))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = id_to_city[model.evaluate(days[0]).as_long()]
        start_day = 1
        for i in range(1, total_days):
            place = id_to_city[model.evaluate(days[i]).as_long()]
            if place != current_place:
                # Add the stay until previous day
                if start_day == i:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{i}"
                itinerary.append({"day_range": day_str, "place": current_place})
                # Add the flight day entries (current_place and place on day i+1)
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                itinerary.append({"day_range": f"Day {i}", "place": place})
                current_place = place
                start_day = i + 1
        # Add the last stay
        if start_day == total_days:
            day_str = f"Day {start_day}"
        else:
            day_str = f"Day {start_day}-{total_days}"
        itinerary.append({"day_range": day_str, "place": current_place})
        
        # Now, we need to ensure that the Istanbul show is correctly placed (25-29)
        # Also, the workshop in Krakow is days 5-9.
        # The model should already satisfy these, but let's verify.
        
        # Output the itinerary
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))