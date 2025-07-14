import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Naples", "Valencia", "Stuttgart", "Split", "Venice", "Amsterdam", "Nice", "Barcelona", "Porto"]
    
    # Direct flights as adjacency list
    direct_flights = {
        "Venice": ["Nice", "Amsterdam", "Stuttgart", "Naples", "Barcelona"],
        "Naples": ["Amsterdam", "Split", "Nice", "Valencia", "Barcelona", "Stuttgart", "Venice"],
        "Barcelona": ["Nice", "Porto", "Valencia", "Naples", "Venice", "Amsterdam", "Stuttgart", "Split"],
        "Amsterdam": ["Naples", "Nice", "Valencia", "Porto", "Split", "Venice", "Stuttgart", "Barcelona"],
        "Nice": ["Venice", "Barcelona", "Amsterdam", "Naples", "Porto"],
        "Stuttgart": ["Valencia", "Porto", "Split", "Amsterdam", "Naples", "Venice", "Barcelona"],
        "Valencia": ["Stuttgart", "Amsterdam", "Naples", "Porto", "Barcelona"],
        "Split": ["Stuttgart", "Naples", "Amsterdam", "Barcelona"],
        "Porto": ["Stuttgart", "Barcelona", "Nice", "Amsterdam", "Valencia"]
    }
    
    # Duration constraints
    durations = {
        "Naples": 3,
        "Valencia": 5,
        "Stuttgart": 2,
        "Split": 5,
        "Venice": 5,
        "Amsterdam": 4,
        "Nice": 2,
        "Barcelona": 2,
        "Porto": 4
    }
    
    # Event constraints
    # Venice: conference between day 6-10 (must be in Venice for some of these days, but the problem says during day 6 and day 10, so assume at least days 6-10 are in Venice)
    # Barcelona: workshop between day 5-6 (must be in Barcelona on day 5 or 6)
    # Naples: meet friend between day 18-20 (must be in Naples on at least one of these days)
    # Nice: meet friends between day 23-24 (must be in Nice on at least one of these days)
    
    # Initialize Z3 solver
    solver = Solver()
    
    # Variables: for each day, which city are you in?
    day_to_city = [Int(f"day_{i}_city") for i in range(1, 25)]
    # Map city names to integers
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints that each day's city is within 0..8
    for day_var in day_to_city:
        solver.add(day_var >= 0, day_var < len(cities))
    
    # Flight transitions: consecutive days must be either same city or connected by direct flight
    for i in range(24 - 1):
        current_day = day_to_city[i]
        next_day = day_to_city[i + 1]
        # Either stay in the same city or move to a connected city
        solver.add(Or(
            current_day == next_day,
            *[And(current_day == city_to_int[a], next_day == city_to_int[b]) 
              for a in direct_flights for b in direct_flights[a] if a in city_to_int and b in city_to_int]
        ))
    
    # Duration constraints: total days in each city must match the required duration
    for city in cities:
        total_days = Sum([If(day_to_city[i] == city_to_int[city], 1, 0) for i in range(24)])
        solver.add(total_days == durations[city])
    
    # Event constraints
    # Venice: conference between day 6-10 (1-based: days 5-9 in 0-based)
    solver.add(Or(*[day_to_city[i] == city_to_int["Venice"] for i in range(5, 10)]))
    
    # Barcelona: workshop between day 5-6 (1-based: days 4-5 in 0-based)
    solver.add(Or(day_to_city[4] == city_to_int["Barcelona"], day_to_city[5] == city_to_int["Barcelona"]))
    
    # Naples: meet friend between day 18-20 (1-based: days 17-19 in 0-based)
    solver.add(Or(*[day_to_city[i] == city_to_int["Naples"] for i in range(17, 20)]))
    
    # Nice: meet friends between day 23-24 (1-based: days 22-23 in 0-based)
    solver.add(Or(day_to_city[22] == city_to_int["Nice"], day_to_city[23] == city_to_int["Nice"]))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        # Helper to add entries to itinerary
        def add_entry(s_day, e_day, city):
            if s_day == e_day:
                itinerary.append({"day_range": f"Day {s_day}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": city})
        
        # Process each day to find consecutive days in the same city
        for day in range(1, 25):
            city_idx = model.evaluate(day_to_city[day - 1]).as_long()
            city = int_to_city[city_idx]
            
            if day == 1:
                current_city = city
                start_day = 1
            else:
                if city == current_city:
                    continue
                else:
                    # Add the previous city's stay
                    add_entry(start_day, day - 1, current_city)
                    # Add flight day entries for previous city and new city
                    itinerary.append({"day_range": f"Day {day - 1}", "place": current_city})
                    itinerary.append({"day_range": f"Day {day - 1}", "place": city})
                    current_city = city
                    start_day = day
        
        # Add the last city's stay
        add_entry(start_day, 24, current_city)
        
        # Now, handle flight days where the same day appears for two cities
        # We need to process the itinerary to insert flight days correctly
        # Reconstruct the itinerary by checking for consecutive same-day entries
        final_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            entry = itinerary[i]
            day_range = entry["day_range"]
            if day_range.startswith("Day ") and '-' not in day_range:
                day = int(day_range.split()[1])
                # Check if next entry is same day
                if i + 1 < n and itinerary[i+1]["day_range"] == day_range:
                    # Flight day: both cities on same day
                    final_itinerary.append(entry)
                    final_itinerary.append(itinerary[i+1])
                    i += 2
                    # The next entry should start from day+1
                    continue
            final_itinerary.append(entry)
            i += 1
        
        return {"itinerary": final_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))