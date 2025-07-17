from z3 import *

# Define the cities and their required stay durations
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

# Define the direct flight connections
flights = {
    ("Reykjavik", "Stuttgart"), ("Stuttgart", "Split"), ("Stuttgart", "Vienna"),
    ("Prague", "Manchester"), ("Edinburgh", "Prague"), ("Manchester", "Split"),
    ("Prague", "Vienna"), ("Vienna", "Manchester"), ("Prague", "Split"),
    ("Vienna", "Lyon"), ("Stuttgart", "Edinburgh"), ("Split", "Lyon"),
    ("Stuttgart", "Manchester"), ("Prague", "Lyon"), ("Reykjavik", "Vienna"),
    ("Prague", "Reykjavik"), ("Vienna", "Split")
}

# Create a solver instance
solver = Solver()

# Define the variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Define the constraints
for city, days in cities.items():
    # Each city must start on a day >= 1 and end on a day <= 25
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + days <= 25)

# Add the specific constraints for each city
solver.add(start_days["Edinburgh"] == 5)  # Annual show in Edinburgh from day 5 to day 8
solver.add(start_days["Split"] >= 19)     # Wedding in Split between day 19 and day 23
solver.add(start_days["Split"] <= 19)     # Wedding in Split between day 19 and day 23

# Add constraints for transitions between cities
for (city1, city2) in flights:
    # If you leave city1 on day X, you must arrive in city2 on day X
    # This means the start day of city2 must be <= the end day of city1
    solver.add(Or(start_days[city2] <= start_days[city1], start_days[city1] + cities[city1] <= start_days[city2]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model[start_days[city]].as_long()
        end_day = start_day + cities[city] - 1
        itinerary.append({"day": start_day, "city": city})
        itinerary.append({"day": end_day, "city": city})
    
    # Sort the itinerary by day
    itinerary.sort(key=lambda x: x["day"])
    
    # Create the final JSON output
    final_itinerary = []
    current_day = 1
    current_city = None
    for entry in itinerary:
        if entry["day"] == current_day:
            if current_city is not None and current_city != entry["city"]:
                final_itinerary.append({"day": current_day, "city": current_city})
            current_city = entry["city"]
        else:
            final_itinerary.append({"day": current_day, "city": current_city})
            current_day = entry["day"]
            current_city = entry["city"]
    final_itinerary.append({"day": current_day, "city": current_city})
    
    # Remove consecutive duplicate entries
    final_itinerary = [entry for i, entry in enumerate(final_itinerary) if i == 0 or final_itinerary[i-1] != entry]
    
    # Print the final itinerary in JSON format
    import json
    print(json.dumps({"itinerary": final_itinerary}, indent=2))
else:
    print("No solution found")