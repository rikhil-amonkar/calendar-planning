import json
from z3 import *

def solve_itinerary():
    # Cities with corrected spellings
    cities = [
        "Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw",
        "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"
    ]
    
    # Corrected direct flights (ensuring all city names match exactly)
    direct_flights = {
        "Budapest": ["Munich", "Vienna", "Warsaw", "Bucharest", "Edinburgh", "Barcelona"],
        "Bucharest": ["Riga", "Munich", "Warsaw", "Vienna", "Budapest", "Barcelona"],
        "Munich": ["Budapest", "Krakow", "Warsaw", "Bucharest", "Barcelona", "Stockholm", "Edinburgh", "Vienna"],
        "Krakow": ["Munich", "Warsaw", "Edinburgh", "Stockholm", "Vienna", "Barcelona"],
        "Barcelona": ["Warsaw", "Munich", "Stockholm", "Riga", "Edinburgh", "Budapest", "Bucharest", "Krakow", "Vienna"],
        "Warsaw": ["Munich", "Krakow", "Barcelona", "Bucharest", "Vienna", "Budapest", "Riga", "Stockholm"],
        "Stockholm": ["Edinburgh", "Krakow", "Munich", "Barcelona", "Riga", "Warsaw", "Vienna"],
        "Riga": ["Bucharest", "Barcelona", "Vienna", "Munich", "Warsaw", "Stockholm", "Edinburgh"],
        "Edinburgh": ["Stockholm", "Krakow", "Barcelona", "Budapest", "Munich", "Riga"],
        "Vienna": ["Budapest", "Riga", "Krakow", "Warsaw", "Stockholm", "Munich", "Bucharest", "Barcelona"]
    }
    
    # Required days per city
    required_days = {
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
    
    # Fixed events with corrected day ranges
    fixed_events = [
        (18, 20, "Munich"),  # Workshop in Munich (3 days)
        (25, 29, "Warsaw"),  # Conference in Warsaw (5 days)
        (9, 13, "Budapest"), # Annual show in Budapest (5 days)
        (17, 18, "Stockholm"), # Meet friends in Stockholm (2 days)
        (1, 5, "Edinburgh")   # Meet friend in Edinburgh (5 days)
    ]
    
    # Create Z3 solver
    s = Solver()
    
    # Variables: each day is assigned a city
    day_to_city = [Int(f"day_{i}") for i in range(1, 33)]
    for day in day_to_city:
        s.add(day >= 0, day < len(cities))
    
    # Fixed events constraints
    for start, end, city in fixed_events:
        city_idx = cities.index(city)
        for day in range(start, end + 1):
            s.add(day_to_city[day - 1] == city_idx)
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(31):
        current_day = day_to_city[i]
        next_day = day_to_city[i + 1]
        # Either stay in same city or move to directly connected city
        same_city = (current_day == next_day)
        possible_flights = []
        for c_idx in range(len(cities)):
            current_city = cities[c_idx]
            for neighbor in direct_flights.get(current_city, []):
                neighbor_idx = cities.index(neighbor)
                possible_flights.append(And(current_day == c_idx, next_day == neighbor_idx))
        s.add(Or(same_city, *possible_flights))
    
    # Duration constraints with proper counting
    for city_idx, city in enumerate(cities):
        count = 0
        for day in day_to_city:
            count += If(day == city_idx, 1, 0)
        s.add(count == required_days[city])
    
    # Additional constraints to break symmetries and help solver
    # Ensure first day is Edinburgh (from fixed events)
    s.add(day_to_city[0] == cities.index("Edinburgh"))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 33):
            city_idx = model.evaluate(day_to_city[day - 1]).as_long()
            itinerary.append({"day": day, "place": cities[city_idx]})
        
        # Verify all constraints are met
        # Count days per city
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            day_counts[entry["place"]] += 1
        
        # Check flight transitions
        valid = True
        for i in range(31):
            current_city = itinerary[i]["place"]
            next_city = itinerary[i + 1]["place"]
            if current_city != next_city and next_city not in direct_flights[current_city]:
                valid = False
                break
        
        if valid and all(day_counts[city] == required_days[city] for city in cities):
            return {"itinerary": itinerary}
        else:
            return {"error": "Solution found but failed validation"}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the solution
solution = solve_itinerary()
print(json.dumps(solution, indent=2))