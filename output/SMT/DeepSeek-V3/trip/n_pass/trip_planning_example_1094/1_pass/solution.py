import json
from z3 import *

# Define the cities and their required days
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

# Define the direct flights as a set of tuples
direct_flights = {
    ("Hamburg", "Stockholm"),
    ("Vienna", "Stockholm"),
    ("Paris", "Edinburgh"),
    ("Riga", "Barcelona"),
    ("Paris", "Riga"),
    ("Krakow", "Barcelona"),
    ("Edinburgh", "Stockholm"),
    ("Paris", "Krakow"),
    ("Krakow", "Stockholm"),
    ("Riga", "Edinburgh"),
    ("Barcelona", "Stockholm"),
    ("Paris", "Stockholm"),
    ("Krakow", "Edinburgh"),
    ("Vienna", "Hamburg"),
    ("Paris", "Hamburg"),
    ("Riga", "Stockholm"),
    ("Hamburg", "Barcelona"),
    ("Vienna", "Barcelona"),
    ("Krakow", "Vienna"),
    ("Riga", "Hamburg"),  # Note: The original list says "from Riga to Hamburg", so direction may matter
    ("Barcelona", "Edinburgh"),
    ("Paris", "Barcelona"),
    ("Hamburg", "Edinburgh"),
    ("Paris", "Vienna"),
    ("Vienna", "Riga")
}

# Make sure flights are bidirectional
bidirectional_flights = set()
for (a, b) in direct_flights:
    bidirectional_flights.add((a, b))
    bidirectional_flights.add((b, a))
direct_flights = bidirectional_flights

# Create a Z3 solver
s = Solver()

# Days are 1..16
days = 16
day_numbers = range(1, days + 1)

# Create variables: for each day, which city are we in?
city_vars = [Int(f"day_{i}") for i in day_numbers]

# Assign each city a unique integer
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Constraints: each day's variable must be one of the city IDs
for day_var in city_vars:
    s.add(Or([day_var == city_ids[city] for city in cities]))

# Constraints for specific events:
# Wedding in Paris on day 1 and 2
s.add(city_vars[0] == city_ids["Paris"])  # day 1
s.add(city_vars[1] == city_ids["Paris"])  # day 2

# Conference in Hamburg on day 10 and 11 (indices 9 and 10)
s.add(city_vars[9] == city_ids["Hamburg"])  # day 10
s.add(city_vars[10] == city_ids["Hamburg"])  # day 11

# Meet friend in Edinburgh between day 12 and 15 (indices 11 to 14)
s.add(Or([city_vars[i] == city_ids["Edinburgh"] for i in range(11, 14 + 1)]))

# Relatives in Stockholm between day 15 and 16 (indices 14 and 15)
s.add(Or(city_vars[14] == city_ids["Stockholm"], city_vars[15] == city_ids["Stockholm"]))

# Flight constraints: consecutive days must be same city or connected by a direct flight
for i in range(days - 1):
    current_day = city_vars[i]
    next_day = city_vars[i + 1]
    # Either stay in the same city or move to a directly connected city
    s.add(Or(
        current_day == next_day,
        *[
            And(current_day == city_ids[a], next_day == city_ids[b])
            for (a, b) in direct_flights
        ]
    ))

# Constraints for total days in each city
for city, required_days in cities.items():
    city_id = city_ids[city]
    total_days = Sum([If(city_vars[i] == city_id, 1, 0) for i in range(days)])
    s.add(total_days == required_days)

# Solve the problem
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(days):
        city_id = m.evaluate(city_vars[i]).as_long()
        city = id_to_city[city_id]
        itinerary.append({"day": i + 1, "place": city})
    
    # Verify the itinerary meets all constraints
    # Check days in each city
    city_days = {city: 0 for city in cities}
    for entry in itinerary:
        city_days[entry["place"]] += 1
    
    for city, required in cities.items():
        assert city_days[city] == required, f"City {city} has {city_days[city]} days instead of {required}"
    
    # Check specific events
    assert itinerary[0]["place"] == "Paris" and itinerary[1]["place"] == "Paris", "Wedding in Paris not on days 1-2"
    assert itinerary[9]["place"] == "Hamburg" and itinerary[10]["place"] == "Hamburg", "Conference in Hamburg not on days 10-11"
    assert any(itinerary[i]["place"] == "Edinburgh" for i in range(11, 14 + 1)), "Edinburgh friend visit not between days 12-15"
    assert itinerary[14]["place"] == "Stockholm" or itinerary[15]["place"] == "Stockholm", "Stockholm relatives not visited on days 15-16"
    
    # Check flight connections
    for i in range(days - 1):
        current = itinerary[i]["place"]
        next_ = itinerary[i + 1]["place"]
        if current != next_:
            assert (current, next_) in direct_flights, f"No direct flight from {current} to {next_} on day {i + 1}"
    
    # Output the itinerary as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")