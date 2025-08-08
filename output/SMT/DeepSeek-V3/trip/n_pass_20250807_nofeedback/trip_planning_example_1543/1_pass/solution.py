import json
from z3 import *

# Define the cities and their required days
cities = {
    "Prague": 3,
    "Warsaw": 4,
    "Dublin": 3,
    "Athens": 3,
    "Vilnius": 4,
    "Porto": 5,
    "London": 3,
    "Seville": 2,
    "Lisbon": 5,
    "Dubrovnik": 3
}

# Direct flights as a set of tuples
direct_flights = {
    ("Warsaw", "Vilnius"),
    ("Prague", "Athens"),
    ("London", "Lisbon"),
    ("Lisbon", "Porto"),
    ("Prague", "Lisbon"),
    ("London", "Dublin"),
    ("Athens", "Vilnius"),
    ("Athens", "Dublin"),
    ("Prague", "London"),
    ("London", "Warsaw"),
    ("Dublin", "Seville"),
    ("Seville", "Porto"),
    ("Lisbon", "Athens"),
    ("Dublin", "Porto"),
    ("Athens", "Warsaw"),
    ("Lisbon", "Warsaw"),
    ("Porto", "Warsaw"),
    ("Prague", "Warsaw"),
    ("Prague", "Dublin"),
    ("Athens", "Dubrovnik"),
    ("Lisbon", "Dublin"),
    ("Dubrovnik", "Dublin"),
    ("Lisbon", "Seville"),
    ("London", "Athens")
}

# Make sure flights are bidirectional
additional_flights = set()
for (a, b) in direct_flights:
    additional_flights.add((b, a))
direct_flights.update(additional_flights)

# Create a Z3 solver instance
solver = Solver()

# Create variables for each day (1..26)
days = 26
day_city = [Int(f"day_{i}") for i in range(1, days + 1)]

# Assign each city to an integer
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Constraints for each day to be within city IDs
for day in day_city:
    solver.add(day >= 0, day < len(cities))

# Fixed intervals
# Prague between day 1 and 3 (inclusive)
solver.add(Sum([If(day_city[i] == city_ids["Prague"], 1, 0) for i in range(3)]) == 3)

# London wedding between day 3 and 5: sum of London days in 3-5 is at least 1.
solver.add(Sum([If(day_city[i] == city_ids["London"], 1, 0) for i in range(2, 5)]) >= 1)

# Conference in Porto between day 16 and 20 (inclusive, days 16-20 are 5 days)
solver.add(Sum([If(day_city[i] == city_ids["Porto"], 1, 0) for i in range(15, 20)]) >= 1)

# Friends in Warsaw between day 20 and 23 (inclusive, 4 days)
solver.add(Sum([If(day_city[i] == city_ids["Warsaw"], 1, 0) for i in range(19, 23)]) >= 1)

# Relatives in Lisbon between day 5 and 9 (inclusive, 5 days)
solver.add(Sum([If(day_city[i] == city_ids["Lisbon"], 1, 0) for i in range(4, 9)]) >= 1)

# Flight constraints: consecutive days must be either the same city or connected by a direct flight
for i in range(days - 1):
    current_city = day_city[i]
    next_city = day_city[i + 1]
    solver.add(Or(
        current_city == next_city,
        *[And(current_city == city_ids[a], next_city == city_ids[b]) for (a, b) in direct_flights]
    ))

# Total days per city
for city, required_days in cities.items():
    solver.add(Sum([If(day == city_ids[city], 1, 0) for day in day_city]) == required_days)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(days):
        city_id = model.evaluate(day_city[i]).as_long()
        city = id_to_city[city_id]
        itinerary.append({"day": i + 1, "place": city})
    
    # Verify the itinerary meets all constraints
    # Check city counts
    city_counts = {city: 0 for city in cities}
    for entry in itinerary:
        city_counts[entry["place"]] += 1
    for city, count in city_counts.items():
        assert count == cities[city], f"City {city} has {count} days, expected {cities[city]}"
    
    # Check fixed intervals
    # Prague in days 1-3
    prague_days = [entry["day"] for entry in itinerary if entry["place"] == "Prague"]
    assert all(1 <= day <= 3 for day in prague_days), "Prague not in days 1-3"
    
    # London in days 3-5
    london_days = [entry["day"] for entry in itinerary if entry["place"] == "London"]
    assert any(3 <= day <= 5 for day in london_days), "London not in days 3-5"
    
    # Porto in days 16-20
    porto_days = [entry["day"] for entry in itinerary if entry["place"] == "Porto"]
    assert any(16 <= day <= 20 for day in porto_days), "Porto not in days 16-20"
    
    # Warsaw in days 20-23
    warsaw_days = [entry["day"] for entry in itinerary if entry["place"] == "Warsaw"]
    assert any(20 <= day <= 23 for day in warsaw_days), "Warsaw not in days 20-23"
    
    # Lisbon in days 5-9
    lisbon_days = [entry["day"] for entry in itinerary if entry["place"] == "Lisbon"]
    assert any(5 <= day <= 9 for day in lisbon_days), "Lisbon not in days 5-9"
    
    # Check flight connections
    for i in range(len(itinerary) - 1):
        current = itinerary[i]["place"]
        next_ = itinerary[i + 1]["place"]
        if current != next_:
            assert (current, next_) in direct_flights, f"No direct flight from {current} to {next_}"
    
    # Output the itinerary as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")