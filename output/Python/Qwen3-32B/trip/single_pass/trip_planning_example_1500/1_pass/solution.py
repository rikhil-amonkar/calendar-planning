import json

# Define the order of cities and their required days
order = [
    ("London", 3),
    ("Milan", 5),
    ("Zurich", 2),
    ("Stockholm", 2),
    ("Reykjavik", 5),
    ("Stuttgart", 5),
    ("Hamburg", 5),
    ("Bucharest", 2),
    ("Barcelona", 4),
    ("Tallinn", 4),
]

# Define direct flights as a set of bidirectional pairs
direct_flights = {
    # London and Hamburg
    ("London", "Hamburg"), ("Hamburg", "London"),
    # London and Reykjavik
    ("London", "Reykjavik"), ("Reykjavik", "London"),
    # Milan and Barcelona
    ("Milan", "Barcelona"), ("Barcelona", "Milan"),
    # Reykjavik and Barcelona
    ("Reykjavik", "Barcelona"), ("Barcelona", "Reykjavik"),
    # Reykjavik to Stuttgart
    ("Reykjavik", "Stuttgart"), ("Stuttgart", "Reykjavik"),
    # Stockholm and Reykjavik
    ("Stockholm", "Reykjavik"), ("Reykjavik", "Stockholm"),
    # London and Stuttgart
    ("London", "Stuttgart"), ("Stuttgart", "London"),
    # Milan and Zurich
    ("Milan", "Zurich"), ("Zurich", "Milan"),
    # London and Barcelona
    ("London", "Barcelona"), ("Barcelona", "London"),
    # Stockholm and Hamburg
    ("Stockholm", "Hamburg"), ("Hamburg", "Stockholm"),
    # Zurich and Barcelona
    ("Zurich", "Barcelona"), ("Barcelona", "Zurich"),
    # Stockholm and Stuttgart
    ("Stockholm", "Stuttgart"), ("Stuttgart", "Stockholm"),
    # Milan and Hamburg
    ("Milan", "Hamburg"), ("Hamburg", "Milan"),
    # Stockholm and Tallinn
    ("Stockholm", "Tallinn"), ("Tallinn", "Stockholm"),
    # Hamburg and Bucharest
    ("Hamburg", "Bucharest"), ("Bucharest", "Hamburg"),
    # London and Bucharest
    ("London", "Bucharest"), ("Bucharest", "London"),
    # Milan and Stockholm
    ("Milan", "Stockholm"), ("Stockholm", "Milan"),
    # Milan and Stuttgart
    ("Milan", "Stuttgart"), ("Stuttgart", "Milan"),
    # Stockholm and Barcelona
    ("Stockholm", "Barcelona"), ("Barcelona", "Stockholm"),
    # London and Milan
    ("London", "Milan"), ("Milan", "London"),
    # Zurich and Hamburg
    ("Zurich", "Hamburg"), ("Hamburg", "Zurich"),
    # Bucharest and Barcelona
    ("Bucharest", "Barcelona"), ("Barcelona", "Bucharest"),
    # Zurich and Stockholm
    ("Zurich", "Stockholm"), ("Stockholm", "Zurich"),
    # Barcelona and Tallinn
    ("Barcelona", "Tallinn"), ("Tallinn", "Barcelona"),
    # Hamburg and Barcelona
    ("Hamburg", "Barcelona"), ("Barcelona", "Hamburg"),
    # Stuttgart and Barcelona
    ("Stuttgart", "Barcelona"), ("Barcelona", "Stuttgart"),
    # Zurich and Tallinn
    ("Zurich", "Tallinn"), ("Tallinn", "Zurich"),
    # Zurich and Bucharest
    ("Zurich", "Bucharest"), ("Bucharest", "Zurich"),
}

direct_flights = set(direct_flights)  # Convert to a set for fast lookups

# Generate the itinerary
itinerary_data = []
current_day = 1

for city, days in order:
    start_day = current_day
    end_day = start_day + days - 1
    itinerary_data.append({
        "city": city,
        "start_day": start_day,
        "end_day": end_day
    })
    current_day = end_day  # Next city starts on this day

# Check transitions between cities
for i in range(1, len(itinerary_data)):
    prev_city = itinerary_data[i-1]["city"]
    current_city = itinerary_data[i]["city"]
    if (prev_city, current_city) not in direct_flights:
        raise ValueError(f"No direct flight from {prev_city} to {current_city}")

# Format the itinerary into the required JSON structure
itinerary = []
for entry in itinerary_data:
    day_range = f"Day {entry['start_day']}-{entry['end_day']}"
    itinerary.append({
        "day_range": day_range,
        "place": entry["city"]
    })

# Output the JSON
json_output = {"itinerary": itinerary}
print(json.dumps(json_output, indent=2))