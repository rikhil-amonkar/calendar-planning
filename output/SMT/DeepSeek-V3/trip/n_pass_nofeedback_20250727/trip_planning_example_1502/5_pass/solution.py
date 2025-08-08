from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = [
        "Santorini",
        "Valencia",
        "Madrid",
        "Seville",
        "Bucharest",
        "Vienna",
        "Riga",
        "Tallinn",
        "Krakow",
        "Frankfurt"
    ]
    
    # Create bidirectional flight connections
    flight_pairs = [
        ("Vienna", "Bucharest"),
        ("Vienna", "Seville"),
        ("Vienna", "Valencia"),
        ("Vienna", "Madrid"),
        ("Vienna", "Krakow"),
        ("Vienna", "Frankfurt"),
        ("Vienna", "Riga"),
        ("Vienna", "Santorini"),
        ("Bucharest", "Riga"),
        ("Bucharest", "Valencia"),
        ("Bucharest", "Santorini"),
        ("Bucharest", "Frankfurt"),
        ("Bucharest", "Madrid"),
        ("Santorini", "Madrid"),
        ("Madrid", "Valencia"),
        ("Madrid", "Seville"),
        ("Madrid", "Frankfurt"),
        ("Seville", "Valencia"),
        ("Valencia", "Krakow"),
        ("Valencia", "Frankfurt"),
        ("Riga", "Frankfurt"),
        ("Riga", "Tallinn"),
        ("Tallinn", "Frankfurt"),
        ("Krakow", "Frankfurt")
    ]
    
    # Create flight dictionary
    direct_flights = {city: [] for city in cities}
    for a, b in flight_pairs:
        if b not in direct_flights[a]:
            direct_flights[a].append(b)
        if a not in direct_flights[b]:
            direct_flights[b].append(a)
    
    # Total days
    total_days = 27
    
    # Create solver
    solver = Solver()
    
    # Create variables: for each day, which city are you in?
    day_city = [Int(f"day_{day}_city") for day in range(total_days)]
    
    # City indices
    city_index = {city: idx for idx, city in enumerate(cities)}
    index_city = {idx: city for idx, city in enumerate(cities)}
    
    # Each day must be assigned to a valid city
    for day in range(total_days):
        solver.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Constraints for each city's total days
    constraints = [
        ("Santorini", 3),
        ("Valencia", 4),
        ("Madrid", 2),
        ("Seville", 2),
        ("Bucharest", 3),
        ("Vienna", 4),
        ("Riga", 4),
        ("Tallinn", 5),
        ("Krakow", 5),
        ("Frankfurt", 4)
    ]
    
    for city, days in constraints:
        solver.add(Sum([If(day_city[day] == city_index[city], 1, 0) 
                      for day in range(total_days)]) == days)
    
    # Fixed events
    # Madrid show on days 6-7 (0-based: 5-6)
    solver.add(day_city[5] == city_index["Madrid"])
    solver.add(day_city[6] == city_index["Madrid"])
    
    # Vienna wedding between days 3-6 (0-based: 2-5)
    solver.add(Or([day_city[day] == city_index["Vienna"] for day in range(2, 6)]))
    
    # Riga conference days 20-23 (0-based: 19-22)
    for day in range(19, 23):
        solver.add(day_city[day] == city_index["Riga"])
    
    # Tallinn workshop days 23-27 (0-based: 22-26)
    for day in range(22, 26):
        solver.add(day_city[day] == city_index["Tallinn"])
    
    # Krakow friends days 11-15 (0-based: 10-14)
    for day in range(10, 15):
        solver.add(day_city[day] == city_index["Krakow"])
    
    # Flight constraints
    for day in range(total_days - 1):
        current = day_city[day]
        next_ = day_city[day + 1]
        solver.add(Or(
            current == next_,
            *[And(current == city_index[a], next_ == city_index[b]) 
              for a in direct_flights 
              for b in direct_flights[a] if a != b]
        ))
    
    # Additional constraints to help the solver
    # Limit consecutive city changes
    solver.add(Sum([If(day_city[day] != day_city[day + 1], 1, 0) 
                   for day in range(total_days - 1)]) <= 12)
    
    # Check solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(total_days):
            city_idx = model.evaluate(day_city[day]).as_long()
            itinerary.append({"day": day + 1, "place": index_city[city_idx]})
        
        # Verify all constraints
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry["place"]] += 1
        
        for city, days in constraints:
            assert city_counts[city] == days, f"Failed for {city}"
        
        # Verify fixed events
        assert itinerary[5]["place"] == "Madrid"
        assert itinerary[6]["place"] == "Madrid"
        assert any(itinerary[day]["place"] == "Vienna" for day in range(2, 6))
        assert all(itinerary[day]["place"] == "Riga" for day in range(19, 23))
        assert all(itinerary[day]["place"] == "Tallinn" for day in range(22, 26))
        assert all(itinerary[day]["place"] == "Krakow" for day in range(10, 15))
        
        # Verify flight connections
        for day in range(total_days - 1):
            current = itinerary[day]["place"]
            next_ = itinerary[day + 1]["place"]
            if current != next_:
                assert next_ in direct_flights[current], f"No flight from {current} to {next_}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))