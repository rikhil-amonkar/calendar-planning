from z3 import *

def solve_itinerary():
    # Cities to visit
    cities = ["London", "Zurich", "Bucharest", "Hamburg", "Barcelona", 
              "Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Milan"]
    
    # Total days
    days = 28
    
    # Create solver
    s = Solver()
    
    # City indices
    city_index = {city: idx for idx, city in enumerate(cities)}
    num_cities = len(cities)
    
    # Day assignments (0..num_cities-1)
    itinerary = [Int(f"day_{day}") for day in range(1, days + 1)]
    
    # Each day must be a valid city index
    for day_var in itinerary:
        s.add(day_var >= 0, day_var < num_cities)
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("London", "Hamburg"), ("London", "Reykjavik"), ("Milan", "Barcelona"),
        ("Reykjavik", "Barcelona"), ("Reykjavik", "Stuttgart"), ("Stockholm", "Reykjavik"),
        ("London", "Stuttgart"), ("Milan", "Zurich"), ("London", "Barcelona"),
        ("Stockholm", "Hamburg"), ("Zurich", "Barcelona"), ("Stockholm", "Stuttgart"),
        ("Milan", "Hamburg"), ("Stockholm", "Tallinn"), ("Hamburg", "Bucharest"),
        ("London", "Bucharest"), ("Milan", "Stockholm"), ("Stuttgart", "Hamburg"),
        ("London", "Zurich"), ("Milan", "Reykjavik"), ("London", "Stockholm"),
        ("Milan", "Stuttgart"), ("Stockholm", "Barcelona"), ("London", "Milan"),
        ("Zurich", "Hamburg"), ("Bucharest", "Barcelona"), ("Zurich", "Stockholm"),
        ("Barcelona", "Tallinn"), ("Zurich", "Tallinn"), ("Hamburg", "Barcelona"),
        ("Stuttgart", "Barcelona"), ("Zurich", "Reykjavik"), ("Zurich", "Bucharest")
    ]
    
    # Create flight pairs as city indices
    flight_pairs = set()
    for a, b in direct_flights:
        a_idx = city_index[a]
        b_idx = city_index[b]
        flight_pairs.add((a_idx, b_idx))
        flight_pairs.add((b_idx, a_idx))
    
    # Flight constraints
    for i in range(days - 1):
        current = itinerary[i]
        next_city = itinerary[i + 1]
        s.add(Or(current == next_city, (current, next_city) in flight_pairs))
    
    # Fixed day constraints
    # London days 1-3 (indices 0-2)
    for day in [0, 1, 2]:
        s.add(itinerary[day] == city_index["London"])
    
    # Zurich days 7-8 (indices 6-7)
    s.add(itinerary[6] == city_index["Zurich"])
    s.add(itinerary[7] == city_index["Zurich"])
    
    # Reykjavik days 9-13 (indices 8-12)
    for day in range(8, 13):
        s.add(itinerary[day] == city_index["Reykjavik"])
    
    # Milan days 3-7 (indices 2-6)
    for day in [2, 3, 4, 5, 6]:
        s.add(itinerary[day] == city_index["Milan"])
    
    # Duration constraints
    duration_requirements = {
        "London": 3,
        "Zurich": 2,
        "Bucharest": 2,
        "Hamburg": 5,
        "Barcelona": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Stockholm": 2,
        "Tallinn": 4,
        "Milan": 5
    }
    
    for city, req_days in duration_requirements.items():
        city_days = Sum([If(itinerary[day] == city_index[city], 1, 0) for day in range(days)])
        s.add(city_days == req_days)
    
    # Additional constraints to help the solver
    # Ensure we visit all required cities
    for city in cities:
        s.add(Or([itinerary[day] == city_index[city] for day in range(days)]))
    
    # Solve with a timeout
    s.set("timeout", 60000)  # 60 seconds timeout
    if s.check() == sat:
        model = s.model()
        result = []
        for day in range(days):
            city_idx = model.evaluate(itinerary[day]).as_long()
            result.append({"day": day + 1, "place": cities[city_idx]})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in result:
            counts[entry["place"]] += 1
        
        return {"itinerary": result}
    else:
        return {"error": "No valid itinerary found"}

# Run and print result
print(solve_itinerary())