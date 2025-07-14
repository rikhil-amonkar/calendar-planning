from z3 import *
import json

def solve_itinerary():
    # Cities and required days
    cities = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }
    
    # Direct flights (undirected)
    direct_flights = {
        "Reykjavik": ["Stuttgart", "Vienna", "Prague"],
        "Stuttgart": ["Reykjavik", "Split", "Vienna", "Edinburgh", "Manchester"],
        "Vienna": ["Stuttgart", "Prague", "Manchester", "Lyon", "Split", "Reykjavik"],
        "Prague": ["Manchester", "Edinburgh", "Vienna", "Split", "Lyon", "Reykjavik"],
        "Edinburgh": ["Prague", "Stuttgart"],
        "Manchester": ["Prague", "Vienna", "Split", "Stuttgart"],
        "Split": ["Stuttgart", "Manchester", "Vienna", "Prague", "Lyon"],
        "Lyon": ["Vienna", "Split", "Prague"]
    }
    
    # Total days
    total_days = 25
    
    # Special constraints
    # Edinburgh: day 5-8 (must be in Edinburgh during these days)
    # Split wedding: day 19-23 (must be in Split during these days)
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day 1..25 (1-based)
    day_city = [ Int(f"day_{i}_city") for i in range(1, total_days + 1) ]
    
    # Assign each city a unique integer
    city_ids = { city: idx for idx, city in enumerate(cities.keys(), 1) }
    id_to_city = { idx: city for city, idx in city_ids.items() }
    
    # Add constraints: each day_city must be one of the city_ids
    for day in day_city:
        s.add(Or([ day == city_id for city_id in city_ids.values() ]))
    
    # Constraint: Edinburgh must be days 5-8
    for day in range(5, 9):  # days 5 to 8 (1-based)
        s.add(day_city[day - 1] == city_ids["Edinburgh"])
    
    # Constraint: Split must include days 19-23
    for day in range(19, 24):  # days 19 to 23
        s.add(day_city[day - 1] == city_ids["Split"])
    
    # Constraint: total days per city
    for city, required_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([ If(day == city_id, 1, 0) for day in day_city ]) == required_days)
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(total_days - 1):
        current_day = day_city[i]
        next_day = day_city[i + 1]
        # If different, must have a direct flight
        s.add(Implies(current_day != next_day, 
                      Or([ And(current_day == city_ids[city1], next_day == city_ids[city2]) 
                          for city1 in direct_flights 
                          for city2 in direct_flights[city1] if city1 in city_ids and city2 in city_ids ])))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary_days = []
        for i in range(total_days):
            day_num = i + 1
            city_id = model.evaluate(day_city[i]).as_long()
            city = id_to_city[city_id]
            itinerary_days.append((day_num, city))
        
        # Process itinerary_days to create day ranges and flight days
        itinerary = []
        current_place = itinerary_days[0][1]
        start_day = 1
        
        for i in range(1, len(itinerary_days)):
            day_num, place = itinerary_days[i]
            if place != current_place:
                # Add the stay up to day i (since day_num is i+1, the previous stay is up to i)
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                # Add flight day: day i+1 is the transition day
                itinerary.append({"day_range": f"Day {i+1}", "place": current_place})
                itinerary.append({"day_range": f"Day {i+1}", "place": place})
                current_place = place
                start_day = i + 1
        
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))