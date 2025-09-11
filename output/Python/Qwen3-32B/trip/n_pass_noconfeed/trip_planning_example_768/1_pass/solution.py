import json

# Define the cities and their required durations
durations = {
    "Mykonos": 4,
    "Nice": 3,
    "London": 2,
    "Copenhagen": 3,
    "Tallinn": 4,
    "Oslo": 5
}

# Define the order of cities based on logical constraints and direct flight availability
cities_order = ["Mykonos", "London", "Copenhagen", "Tallinn", "Oslo", "Nice"]

# Define the direct flights between cities
direct_flights = {
    ("London", "Copenhagen"),
    ("Copenhagen", "Tallinn"),
    ("Tallinn", "Oslo"),
    ("Mykonos", "London"),
    ("Oslo", "Nice"),
    ("London", "Nice"),
    ("Mykonos", "Nice"),
    ("London", "Oslo"),
    ("Copenhagen", "Nice"),
    ("Copenhagen", "Oslo"),
    # Reverse directions
    ("Copenhagen", "London"),
    ("Tallinn", "Copenhagen"),
    ("Oslo", "Tallinn"),
    ("London", "Mykonos"),
    ("Nice", "Oslo"),
    ("Nice", "London"),
    ("Nice", "Mykonos"),
    ("Oslo", "London"),
    ("Nice", "Copenhagen"),
    ("Oslo", "Copenhagen"),
}

# Validate that the cities_order uses valid direct flights
for i in range(len(cities_order) - 1):
    a = cities_order[i]
    b = cities_order[i + 1]
    if (a, b) not in direct_flights:
        raise ValueError(f"No direct flight from {a} to {b}")

# Compute the itinerary with day ranges
current_day = 1
itinerary_data = []
for city in cities_order:
    duration = durations[city]
    start = current_day
    end = start + duration - 1
    itinerary_data.append({
        "day_range": f"Day {start}-{end}",
        "place": city
    })
    current_day = end  # Next city starts on the same day as this city's end

# Output the result as a JSON-formatted dictionary
print(json.dumps({"itinerary": itinerary_data}, indent=2))