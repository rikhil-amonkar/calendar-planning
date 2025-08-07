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
        direct_flights[a].append(b)
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
    # Santorini: 3 days
    santorini_days = Sum([If(day_city[day] == city_index["Santorini"], 1, 0) for day in range(total_days)])
    solver.add(santorini_days == 3)
    
    # Valencia: 4 days
    valencia_days = Sum([If(day_city[day] == city_index["Valencia"], 1, 0) for day in range(total_days)])
    solver.add(valencia_days == 4)
    
    # Madrid: 2 days, show on day 6-7 (1-based: days 5-6 in 0-based)
    madrid_days = Sum([If(day_city[day] == city_index["Madrid"], 1, 0) for day in range(total_days)])
    solver.add(madrid_days == 2)
    solver.add(day_city[5] == city_index["Madrid"])  # day 6
    solver.add(day_city[6] == city_index["Madrid"])  # day 7
    
    # Seville: 2 days
    seville_days = Sum([If(day_city[day] == city_index["Seville"], 1, 0) for day in range(total_days)])
    solver.add(seville_days == 2)
    
    # Bucharest: 3 days
    bucharest_days = Sum([If(day_city[day] == city_index["Bucharest"], 1, 0) for day in range(total_days)])
    solver.add(bucharest_days == 3)
    
    # Vienna: 4 days, wedding between day 3-6 (1-based: days 2-5 in 0-based)
    vienna_days = Sum([If(day_city[day] == city_index["Vienna"], 1, 0) for day in range(total_days)])
    solver.add(vienna_days == 4)
    # Must be in Vienna for at least one day between days 3-6
    solver.add(Or([day_city[day] == city_index["Vienna"] for day in range(2, 6)]))
    
    # Riga: 4 days, conference day 20-23 (1-based: days 19-22 in 0-based)
    riga_days = Sum([If(day_city[day] == city_index["Riga"], 1, 0) for day in range(total_days)])
    solver.add(riga_days == 4)
    for day in range(19, 23):
        solver.add(day_city[day] == city_index["Riga"])
    
    # Tallinn: 5 days, workshop day 23-27 (1-based: days 22-26 in 0-based)
    tallinn_days = Sum([If(day_city[day] == city_index["Tallinn"], 1, 0) for day in range(total_days)])
    solver.add(tallinn_days == 5)
    for day in range(22, 26):
        solver.add(day_city[day] == city_index["Tallinn"])
    
    # Krakow: 5 days, friends day 11-15 (1-based: days 10-14 in 0-based)
    krakow_days = Sum([If(day_city[day] == city_index["Krakow"], 1, 0) for day in range(total_days)])
    solver.add(krakow_days == 5)
    for day in range(10, 15):
        solver.add(day_city[day] == city_index["Krakow"])
    
    # Frankfurt: 4 days
    frankfurt_days = Sum([If(day_city[day] == city_index["Frankfurt"], 1, 0) for day in range(total_days)])
    solver.add(frankfurt_days == 4)
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for day in range(total_days - 1):
        current = day_city[day]
        next_ = day_city[day + 1]
        solver.add(Or(
            current == next_,
            *[And(current == city_index[a], next_ == city_index[b]) 
              for a in direct_flights 
              for b in direct_flights[a]]
        ))
    
    # Additional constraints to prevent impossible transitions
    # Ensure we don't have too many city changes
    city_changes = Sum([If(day_city[day] != day_city[day + 1], 1, 0) for day in range(total_days - 1)])
    solver.add(city_changes <= 15)  # Reasonable upper bound
    
    # Check if the problem is satisfiable
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
        
        assert city_counts["Santorini"] == 3
        assert city_counts["Valencia"] == 4
        assert city_counts["Madrid"] == 2
        assert city_counts["Seville"] == 2
        assert city_counts["Bucharest"] == 3
        assert city_counts["Vienna"] == 4
        assert city_counts["Riga"] == 4
        assert city_counts["Tallinn"] == 5
        assert city_counts["Krakow"] == 5
        assert city_counts["Frankfurt"] == 4
        
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