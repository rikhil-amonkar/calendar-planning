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
    
    # Direct flight connections (undirected)
    direct_flights = {
        "Vienna": ["Bucharest", "Seville", "Valencia", "Madrid", "Krakow", "Frankfurt", "Riga", "Santorini"],
        "Bucharest": ["Vienna", "Riga", "Valencia", "Santorini", "Frankfurt", "Madrid"],
        "Santorini": ["Madrid", "Bucharest", "Vienna"],
        "Madrid": ["Santorini", "Valencia", "Seville", "Vienna", "Bucharest", "Frankfurt"],
        "Seville": ["Valencia", "Vienna", "Madrid"],
        "Valencia": ["Seville", "Madrid", "Bucharest", "Vienna", "Krakow", "Frankfurt"],
        "Riga": ["Bucharest", "Vienna", "Frankfurt", "Tallinn"],
        "Tallinn": ["Riga", "Frankfurt"],
        "Krakow": ["Valencia", "Vienna", "Frankfurt"],
        "Frankfurt": ["Valencia", "Krakow", "Vienna", "Riga", "Tallinn", "Bucharest", "Madrid"]
    }
    
    # Check for bidirectional flights and ensure all are listed correctly
    # (assuming the provided list is correct)
    
    # Total days
    total_days = 27
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: for each day, which city are you in?
    day_city = [Int(f"day_{day}_city") for day in range(1, total_days + 1)]
    
    # Each day's variable must be an index corresponding to a city
    city_index = {city: idx for idx, city in enumerate(cities)}
    index_city = {idx: city for idx, city in enumerate(cities)}
    
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
    solver.add(day_city[5] == city_index["Madrid"])  # day 6 (1-based)
    solver.add(day_city[6] == city_index["Madrid"])  # day 7 (1-based)
    
    # Seville: 2 days
    seville_days = Sum([If(day_city[day] == city_index["Seville"], 1, 0) for day in range(total_days)])
    solver.add(seville_days == 2)
    
    # Bucharest: 3 days
    bucharest_days = Sum([If(day_city[day] == city_index["Bucharest"], 1, 0) for day in range(total_days)])
    solver.add(bucharest_days == 3)
    
    # Vienna: 4 days, wedding between day 3-6 (1-based: days 2-5 in 0-based)
    vienna_days = Sum([If(day_city[day] == city_index["Vienna"], 1, 0) for day in range(total_days)])
    solver.add(vienna_days == 4)
    # At least one day between day 3 and 6 (1-based: days 2-5) must be Vienna
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
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either stay in the same city or move to a connected city
        solver.add(Or(
            current_city == next_city,
            *[And(current_city == city_index[city], next_city == city_index[connected])
              for city in direct_flights
              for connected in direct_flights[city]
              if connected in city_index and city in city_index]
        ))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(total_days):
            city_idx = model.evaluate(day_city[day]).as_long()
            itinerary.append({"day": day + 1, "place": index_city[city_idx]})
        
        # Verify the total days per city
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry["place"]] += 1
        
        # Check if all constraints are met
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
        
        # Check fixed days
        assert itinerary[5]["place"] == "Madrid"  # day 6
        assert itinerary[6]["place"] == "Madrid"  # day 7
        assert any(itinerary[day]["place"] == "Vienna" for day in range(2, 6))  # wedding days 3-6
        assert all(itinerary[day]["place"] == "Riga" for day in range(19, 23))  # conference days 20-23
        assert all(itinerary[day]["place"] == "Tallinn" for day in range(22, 26))  # workshop days 23-27
        assert all(itinerary[day]["place"] == "Krakow" for day in range(10, 15))  # friends days 11-15
        
        # Verify flight connections
        for day in range(total_days - 1):
            current = itinerary[day]["place"]
            next_place = itinerary[day + 1]["place"]
            if current != next_place:
                assert next_place in direct_flights[current], f"No direct flight from {current} to {next_place} on day {day + 1}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver
result = solve_itinerary()

# Output the result in JSON format
print(json.dumps(result, indent=2))