from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5
    }
    
    # Direct flights
    direct_flights = {
        "Budapest": ["Munich", "Vienna", "Warsaw", "Edinburgh", "Barcelona", "Bucharest"],
        "Bucharest": ["Riga", "Munich", "Warsaw", "Vienna", "Barcelona"],
        "Munich": ["Budapest", "Krakow", "Warsaw", "Bucharest", "Barcelona", "Stockholm", "Edinburgh", "Vienna"],
        "Krakow": ["Munich", "Warsaw", "Edinburgh", "Stockholm", "Vienna", "Barcelona"],
        "Barcelona": ["Warsaw", "Munich", "Stockholm", "Edinburgh", "Riga", "Bucharest", "Krakow", "Budapest", "Vienna"],
        "Warsaw": ["Munich", "Krakow", "Barcelona", "Budapest", "Vienna", "Riga", "Stockholm", "Bucharest"],
        "Stockholm": ["Edinburgh", "Krakow", "Munich", "Barcelona", "Riga", "Warsaw", "Vienna"],
        "Riga": ["Bucharest", "Barcelona", "Vienna", "Warsaw", "Stockholm", "Munich", "Edinburgh"],
        "Edinburgh": ["Stockholm", "Barcelona", "Krakow", "Munich", "Budapest", "Riga"],
        "Vienna": ["Budapest", "Riga", "Krakow", "Munich", "Warsaw", "Stockholm", "Bucharest", "Barcelona"]
    }
    
    # Fixed events
    fixed_events = [
        ("Munich", 18, 20),
        ("Warsaw", 25, 29),
        ("Budapest", 9, 13),
        ("Stockholm", 17, 18),
        ("Edinburgh", 1, 5)
    ]
    
    # Create Z3 variables: day[i] represents the city on day i (1-based)
    days = 32
    day_vars = [Int(f"day_{i}") for i in range(1, days + 1)]
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day must be assigned to a valid city
    for day in day_vars:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Fixed events constraints
    for city, start, end in fixed_events:
        for d in range(start, end + 1):
            s.add(day_vars[d - 1] == city_ids[city])
    
    # Duration constraints: each city must be visited for exactly the required days
    for city, required_days in cities.items():
        total_days = Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(days)])
        s.add(total_days == required_days)
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_ids[city1], next_city == city_ids[city2])
                for city1 in cities
                for city2 in direct_flights.get(city1, [])
            ]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        # Helper to add entries to itinerary
        def add_entry(place, start, end):
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": place})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": place})
        
        # Generate the itinerary
        for day in range(1, days + 1):
            city_id = model.evaluate(day_vars[day - 1]).as_long()
            city = id_to_city[city_id]
            if current_place is None:
                current_place = city
                start_day = day
            elif city != current_place:
                add_entry(current_place, start_day, day - 1)
                # Add flight day entries for both departure and arrival
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_place = city
                start_day = day
        # Add the last segment
        add_entry(current_place, start_day, days)
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))