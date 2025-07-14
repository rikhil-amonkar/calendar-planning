from z3 import *

# Define the solver
solver = Solver()

# Define the cities and their respective stay durations
cities = {
    "Vienna": 4,
    "Barcelona": 2,
    "Edinburgh": 4,
    "Krakow": 3,
    "Riga": 4,
    "Hamburg": 2,
    "Paris": 2,
    "Stockholm": 2
}

# Define specific constraints
constraints = {
    "Edinburgh": (12, 15),
    "Hamburg": (10, 11),
    "Paris": (1, 2),
    "Stockholm": (15, 16)
}

# Create a list of all days
days = range(1, 17)

# Create a dictionary to store the place for each day
place_vars = {day: Int(f"place_{day}") for day in days}

# Map city names to unique integer identifiers
city_to_id = {city: i for i, city in enumerate(cities.keys())}
id_to_city = {i: city for city, i in city_to_id.items()}

# Add constraints for each city's stay duration
for city, duration in cities.items():
    city_id = city_to_id[city]
    # Ensure the city is visited for the specified duration
    for start_day in range(1, 17 - duration + 1):
        # Create a list of constraints for this possible start day
        constraints_for_start = []
        for day in range(start_day, start_day + duration):
            constraints_for_start.append(place_vars[day] == city_id)
        # If the city is not visited starting from this day, add the negation of these constraints
        solver.add(Or(*constraints_for_start) | Or([place_vars[day] != city_id for day in range(start_day, start_day + duration)]))

# Add specific constraints for certain cities
for city, (start, end) in constraints.items():
    city_id = city_to_id[city]
    # Ensure the city is visited within the specified range
    solver.add(And([Or([place_vars[day] == city_id for day in range(start, end + 1)])]))

# Add constraints for direct flights
direct_flights = [
    ("Hamburg", "Stockholm"), ("Vienna", "Stockholm"), ("Paris", "Edinburgh"), ("Riga", "Barcelona"),
    ("Paris", "Riga"), ("Krakow", "Barcelona"), ("Edinburgh", "Stockholm"), ("Paris", "Krakow"),
    ("Krakow", "Stockholm"), ("Riga", "Edinburgh"), ("Barcelona", "Stockholm"), ("Paris", "Stockholm"),
    ("Krakow", "Edinburgh"), ("Vienna", "Hamburg"), ("Paris", "Hamburg"), ("Riga", "Stockholm"),
    ("Hamburg", "Barcelona"), ("Vienna", "Barcelona"), ("Krakow", "Vienna"), ("Riga", "Hamburg")
]

flight_constraints = []
for (city1, city2) in direct_flights:
    id1, id2 = city_to_id[city1], city_to_id[city2]
    for day in range(1, 16):
        # If the city changes on a given day, ensure it's a direct flight
        flight_constraints.append(Or(place_vars[day] != place_vars[day + 1], Or(place_vars[day] == id1, place_vars[day] == id2)))
solver.add(flight_constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in days:
        city_id = model.evaluate(place_vars[day]).as_long()
        city = id_to_city[city_id]
        itinerary.append({"day_range": f"Day {day}", "place": city})
    
    # Merge consecutive days in the same city
    merged_itinerary = []
    current_day = 1
    current_city = itinerary[0]["place"]
    for entry in itinerary[1:]:
        day = int(entry["day_range"].split()[1])
        if entry["place"] == current_city:
            continue
        else:
            merged_itinerary.append({"day_range": f"Day {current_day}-{day-1}", "place": current_city})
            current_day = day
            current_city = entry["place"]
    merged_itinerary.append({"day_range": f"Day {current_day}-16", "place": current_city})
    
    # Add flight days
    final_itinerary = []
    for entry in merged_itinerary:
        start_day, end_day = map(int, entry["day_range"].split("-")[1].split(","))
        if start_day == end_day:
            final_itinerary.append(entry)
        else:
            final_itinerary.append({"day_range": f"Day {start_day}-{end_day-1}", "place": entry["place"]})
            final_itinerary.append({"day_range": f"Day {end_day}", "place": entry["place"]})  # Flight day
            final_itinerary.append({"day_range": f"Day {end_day}", "place": entry["place"]})  # Flight day
    
    # Ensure the itinerary covers exactly 16 days
    final_itinerary = []
    current_day = 1
    current_city = itinerary[0]["place"]
    for entry in itinerary[1:]:
        day = int(entry["day_range"].split()[1])
        if entry["place"] == current_city:
            continue
        else:
            final_itinerary.append({"day_range": f"Day {current_day}-{day-1}", "place": current_city})
            final_itinerary.append({"day_range": f"Day {day}", "place": current_city})  # Flight day
            final_itinerary.append({"day_range": f"Day {day}", "place": entry["place"]})  # Flight day
            current_day = day + 1
            current_city = entry["place"]
    final_itinerary.append({"day_range": f"Day {current_day}-16", "place": current_city})
    
    # Remove duplicate flight days
    cleaned_itinerary = []
    for i, entry in enumerate(final_itinerary):
        if i > 0 and entry["day_range"] == final_itinerary[i-1]["day_range"]:
            continue
        cleaned_itinerary.append(entry)
    
    print({"itinerary": cleaned_itinerary})
else:
    print("No solution found")