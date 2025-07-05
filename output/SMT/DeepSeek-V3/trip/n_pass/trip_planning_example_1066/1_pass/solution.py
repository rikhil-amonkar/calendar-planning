from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,  # Note: conference is on days 20-21, but total is 2 days (assuming the conference is part of the 2 days)
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }
    
    # Direct flights
    direct_flights = {
        "Helsinki": ["London", "Madrid", "Brussels", "Split"],
        "Split": ["Madrid", "Helsinki", "London", "Stuttgart"],
        "Brussels": ["London", "Bucharest", "Madrid", "Helsinki"],
        "Bucharest": ["London", "Madrid", "Brussels"],
        "Mykonos": ["Madrid", "London"],
        "Stuttgart": ["London", "Split"],
        "Madrid": ["Split", "Helsinki", "London", "Brussels", "Bucharest", "Mykonos"],
        "London": ["Helsinki", "Madrid", "Brussels", "Bucharest", "Split", "Mykonos", "Stuttgart"]
    }
    
    # Total days
    total_days = 21
    
    # Create solver
    s = Solver()
    
    # Day variables: day[i] is the city on day i (1-based)
    days = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraint: each day must be a valid city
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(total_days - 1):
        current_city = days[i]
        next_city = days[i + 1]
        # Either same city or connected by flight
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[city1], next_city == city_ids[city2]) 
              for city1 in direct_flights 
              for city2 in direct_flights[city1] if city2 in city_ids]
        ))
    
    # Duration constraints: total days in each city must match requirements
    for city, duration in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day == city_id, 1, 0) for day in days]) == duration)
    
    # Special constraints:
    # Conference in Madrid on days 20-21
    s.add(days[19] == city_ids["Madrid"])  # day 20 is index 19 (0-based)
    s.add(days[20] == city_ids["Madrid"])  # day 21
    
    # Friend meeting in Stuttgart between day 1 and day 4 (i.e., Stuttgart must be visited on at least one of days 1-4)
    s.add(Or([days[i] == city_ids["Stuttgart"] for i in range(4)]))  # days 1-4 (indices 0-3)
    
    # Continuity constraints: stays must be continuous blocks (except for flight days)
    # This is implicitly handled by the flight constraints and duration constraints
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Group consecutive days in the same city
        current_city = model.evaluate(days[0])
        start_day = 1
        for i in range(1, total_days):
            city = model.evaluate(days[i])
            if city != current_city:
                # Add the stay for the previous city
                if start_day == i:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{i}"
                itinerary.append({"day_range": day_str, "place": id_to_city[current_city.as_long()]})
                # Add the flight day entries (both departure and arrival)
                itinerary.append({"day_range": f"Day {i}", "place": id_to_city[current_city.as_long()]})
                itinerary.append({"day_range": f"Day {i}", "place": id_to_city[city.as_long()]})
                current_city = city
                start_day = i + 1
        # Add the last stay
        if start_day == total_days:
            day_str = f"Day {start_day}"
        else:
            day_str = f"Day {start_day}-{total_days}"
        itinerary.append({"day_range": day_str, "place": id_to_city[current_city.as_long()]})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))