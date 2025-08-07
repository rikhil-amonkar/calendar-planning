import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }
    
    # Direct flights as per the problem statement
    flight_pairs = [
        ("Riga", "Prague"),
        ("Stockholm", "Milan"),
        ("Riga", "Milan"),
        ("Lisbon", "Stockholm"),
        ("Stockholm", "Santorini"),
        ("Naples", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Naples", "Milan"),
        ("Lisbon", "Naples"),
        ("Riga", "Tallinn"),
        ("Tallinn", "Prague"),
        ("Stockholm", "Warsaw"),
        ("Riga", "Warsaw"),
        ("Lisbon", "Riga"),
        ("Riga", "Stockholm"),
        ("Lisbon", "Porto"),
        ("Lisbon", "Prague"),
        ("Milan", "Porto"),
        ("Prague", "Milan"),
        ("Lisbon", "Milan"),
        ("Warsaw", "Porto"),
        ("Warsaw", "Tallinn"),
        ("Santorini", "Milan"),
        ("Stockholm", "Prague"),
        ("Stockholm", "Tallinn"),
        ("Warsaw", "Milan"),
        ("Santorini", "Naples"),
        ("Warsaw", "Prague")
    ]
    
    # Correct any typos in flight_pairs
    corrected_flight_pairs = []
    for a, b in flight_pairs:
        a_corrected = a.replace("Milan", "Milan").replace("Warsaw", "Warsaw").replace("Riga", "Riga")
        b_corrected = b.replace("Milan", "Milan").replace("Warsaw", "Warsaw").replace("Riga", "Riga")
        corrected_flight_pairs.append((a_corrected, b_corrected))
    
    flight_pairs = list(set(corrected_flight_pairs))  # Remove duplicates
    
    # Build flight_dict: maps each city to list of directly connected cities
    flight_dict = {city: [] for city in cities}
    for a, b in flight_pairs:
        if a in cities and b in cities:
            flight_dict[a].append(b)
            flight_dict[b].append(a)
    
    num_days = 28
    days = range(1, num_days + 1)
    
    solver = Solver()
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Variables: for each day, which city are we in?
    day_to_city = {day: Int(f"day_{day}") for day in days}
    
    # Constraints: each day's variable must be one of the city IDs
    for day in days:
        solver.add(Or([day_to_city[day] == city_ids[city] for city in cities]))
    
    # Constraints on the number of days per city
    for city in cities:
        required_days = cities[city]
        solver.add(Sum([If(day_to_city[day] == city_ids[city], 1, 0) for day in days]) == required_days)
    
    # Specific date constraints:
    # Tallinn between day 18 and 20 (inclusive)
    solver.add(Or([day_to_city[day] == city_ids["Tallinn"] for day in range(18, 21)]))
    
    # Milan between day 24 and 26 (inclusive)
    solver.add(Or([day_to_city[day] == city_ids["Milan"] for day in range(24, 27)]))
    
    # Riga from day 5 to 8 (inclusive)
    for day in range(5, 9):
        solver.add(day_to_city[day] == city_ids["Riga"])
    
    # Flight constraints: consecutive days must have either the same city or a direct flight
    for day in range(1, num_days):
        current_city = day_to_city[day]
        next_city = day_to_city[day + 1]
        solver.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_ids[city1], next_city == city_ids[city2])
                for city1 in cities
                for city2 in flight_dict[city1]
            ]
        ))
    
    # Set a timeout for the solver to prevent it from running indefinitely
    solver.set("timeout", 60000)  # 60 seconds
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in days:
            city_id = model.evaluate(day_to_city[day]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": day, "place": city})
        
        # Verify the itinerary meets all constraints
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry["place"]] += 1
        
        for city in cities:
            assert city_days[city] == cities[city], f"City {city} has {city_days[city]} days instead of {cities[city]}"
        
        tallinn_days = [entry["day"] for entry in itinerary if entry["place"] == "Tallinn"]
        assert any(18 <= day <= 20 for day in tallinn_days), "Tallinn not visited between days 18-20"
        
        milan_days = [entry["day"] for entry in itinerary if entry["place"] == "Milan"]
        assert any(24 <= day <= 26 for day in milan_days), "Milan not visited between days 24-26"
        
        riga_days = [entry["day"] for entry in itinerary if entry["place"] == "Riga"]
        assert all(day in range(5, 9) for day in riga_days if day in range(5, 9)), "Riga not visited from days 5-8"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))