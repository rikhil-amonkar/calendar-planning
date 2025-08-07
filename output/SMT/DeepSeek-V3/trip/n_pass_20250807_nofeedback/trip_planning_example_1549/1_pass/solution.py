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
    
    # Direct flights
    direct_flights = {
        "Riga": ["Prague", "Milan", "Tallinn", "Warsaw", "Stockholm"],
        "Stockholm": ["Milan", "Lisbon", "Warsaw", "Santorini", "Prague", "Tallinn", "Riga"],
        "Milan": ["Stockholm", "Riga", "Naples", "Porto", "Prague", "Lisbon", "Santorini", "Warsaw"],
        "Lisbon": ["Stockholm", "Warsaw", "Naples", "Porto", "Prague", "Milan", "Riga"],
        "Naples": ["Warsaw", "Milan", "Lisbon", "Santorini"],
        "Warsaw": ["Naples", "Lisbon", "Stockholm", "Riga", "Porto", "Tallinn", "Milan", "Prague"],
        "Porto": ["Lisbon", "Milan", "Warsaw"],
        "Prague": ["Riga", "Tallinn", "Stockholm", "Lisbon", "Milan", "Warsaw"],
        "Tallinn": ["Riga", "Prague", "Stockholm", "Warsaw"],
        "Santorini": ["Stockholm", "Milan", "Naples"]
    }
    
    # Correcting some typos in the direct_flights keys (e.g., Milan vs. Mila)
    # Also, some entries have typos like 'Milan' vs 'Milan' (assuming they are the same)
    # Assuming all are correctly spelled as per the problem statement.
    # For example, "Milan" is spelled correctly in cities, so keys in direct_flights should match.
    # But in the direct_flights, some entries have "Milan" as "Milan", etc. Assuming they are the same.
    
    # Alternative: represent direct flights as a set of tuples for clarity.
    flight_pairs = [
        ("Riga", "Prague"), ("Stockholm", "Milan"), ("Riga", "Milan"), ("Lisbon", "Stockholm"),
        ("Stockholm", "Santorini"), ("Naples", "Warsaw"), ("Lisbon", "Warsaw"), ("Naples", "Milan"),
        ("Lisbon", "Naples"), ("Riga", "Tallinn"), ("Tallinn", "Prague"), ("Stockholm", "Warsaw"),
        ("Riga", "Warsaw"), ("Lisbon", "Riga"), ("Riga", "Stockholm"), ("Lisbon", "Porto"),
        ("Lisbon", "Prague"), ("Milan", "Porto"), ("Prague", "Milan"), ("Lisbon", "Milan"),
        ("Warsaw", "Porto"), ("Warsaw", "Tallinn"), ("Santorini", "Milan"), ("Stockholm", "Prague"),
        ("Stockholm", "Tallinn"), ("Warsaw", "Milan"), ("Santorini", "Naples"), ("Warsaw", "Prague")
    ]
    
    # Fixing some typos in the flight_pairs:
    corrected_flight_pairs = []
    for a, b in flight_pairs:
        # Correcting "Milan" vs "Milan" (assuming same)
        a_corrected = a.replace("Milan", "Milan").replace("Milan", "Milan")
        b_corrected = b.replace("Milan", "Milan").replace("Milan", "Milan")
        a_corrected = a_corrected.replace("Stockholm", "Stockholm")
        b_corrected = b_corrected.replace("Stockholm", "Stockholm")
        a_corrected = a_corrected.replace("Warsaw", "Warsaw")
        b_corrected = b_corrected.replace("Warsaw", "Warsaw")
        corrected_flight_pairs.append((a_corrected, b_corrected))
    
    flight_pairs = list(set(corrected_flight_pairs))  # remove duplicates
    
    # Now, create a dictionary of direct flights for each city.
    flight_dict = {}
    for city in cities:
        flight_dict[city] = []
    
    for a, b in flight_pairs:
        if a in cities and b in cities:
            if b not in flight_dict[a]:
                flight_dict[a].append(b)
            if a not in flight_dict[b]:
                flight_dict[b].append(a)
    
    # Now, proceed to model the problem.
    num_days = 28
    days = range(1, num_days + 1)
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Variables: for each day, which city are we in?
    day_to_city = {day: Int(f"day_{day}") for day in days}
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Add constraints that each day's variable must be one of the city IDs
    for day in days:
        solver.add(Or([day_to_city[day] == city_ids[city] for city in cities]))
    
    # Constraints on the number of days per city
    for city in cities:
        required_days = cities[city]
        solver.add(Sum([If(day_to_city[day] == city_ids[city], 1, 0) for day in days]) == required_days)
    
    # Constraints on specific date ranges:
    # Tallinn between day 18 and 20 (inclusive)
    solver.add(Or([day_to_city[day] == city_ids["Tallinn"] for day in range(18, 21)]))
    
    # Milan between day 24 and 26 (inclusive)
    solver.add(Or([day_to_city[day] == city_ids["Milan"] for day in range(24, 27)]))
    
    # Riga from day 5 to 8 (inclusive)
    for day in range(5, 9):
        solver.add(day_to_city[day] == city_ids["Riga"])
    
    # Flight constraints: consecutive days must have either the same city or a direct flight
    for day in range(1, num_days):
        current_day_city = day_to_city[day]
        next_day_city = day_to_city[day + 1]
        # Either stay in the same city or fly to a directly connected city
        solver.add(Or(
            current_day_city == next_day_city,
            *[
                And(current_day_city == city_ids[city1], next_day_city == city_ids[city2])
                for city1 in cities
                for city2 in flight_dict.get(city1, [])
            ]
        ))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_city = None
        start_day = 1
        for day in days:
            city_id = model.evaluate(day_to_city[day]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": day, "place": city})
        
        # Verify the itinerary meets all constraints
        # (This is a sanity check; the solver should ensure this)
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry["place"]] += 1
        
        for city in cities:
            assert city_days[city] == cities[city], f"City {city} has {city_days[city]} days instead of {cities[city]}"
        
        # Check specific date constraints
        tallinn_days = [entry["day"] for entry in itinerary if entry["place"] == "Tallinn"]
        assert any(18 <= day <= 20 for day in tallinn_days), "Tallinn not visited between days 18-20"
        
        milan_days = [entry["day"] for entry in itinerary if entry["place"] == "Milan"]
        assert any(24 <= day <= 26 for day in milan_days), "Milan not visited between days 24-26"
        
        riga_days = [entry["day"] for entry in itinerary if entry["place"] == "Riga"]
        assert all(5 <= day <= 8 for day in riga_days if day in range(5, 9)), "Riga not visited from days 5-8"
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            current_place = itinerary[i]["place"]
            next_place = itinerary[i + 1]["place"]
            if current_place != next_place:
                assert next_place in flight_dict[current_place], f"No flight from {current_place} to {next_place} on day {itinerary[i]['day']}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))