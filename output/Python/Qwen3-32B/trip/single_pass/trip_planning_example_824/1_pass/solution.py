import json

# Define the cities and their required durations and constraints
cities = {
    "Berlin": {"duration": 5, "start": 1},
    "Split": {"duration": 3, "start": None},
    "Bucharest": {"duration": 3, "start": 13},
    "Riga": {"duration": 5, "start": None},
    "Lisbon": {"duration": 3, "start": None},
    "Tallinn": {"duration": 4, "start": None},
    "Lyon": {"duration": 5, "start": 7}
}

# Define direct flights as a dictionary of allowed connections
direct_flights = {
    "Lisbon": ["Bucharest", "Berlin", "Riga", "Lyon"],
    "Berlin": ["Lisbon", "Split", "Riga", "Tallinn"],
    "Bucharest": ["Lisbon", "Riga", "Lyon"],
    "Riga": ["Lisbon", "Berlin", "Bucharest", "Tallinn"],
    "Split": ["Lyon"],
    "Lyon": ["Split", "Lisbon", "Bucharest", "Riga"],  # Assuming direct flight to Riga
    "Tallinn": ["Riga"]
}

# Define the order of cities in the itinerary
itinerary_order = ["Berlin", "Split", "Lyon", "Riga", "Bucharest", "Tallinn", "Lisbon"]

# Calculate start and end days for each city
itinerary = []
current_day = 1
for city in itinerary_order:
    start_day = current_day
    end_day = start_day + cities[city]["duration"] - 1
    cities[city]["start"] = start_day
    cities[city]["end"] = end_day
    current_day = end_day + 1
    itinerary.append({
        "day_range": f"Day {start_day}-{end_day}",
        "place": city
    })

# Ensure Bucharest starts on day 13
if cities["Bucharest"]["start"] != 13:
    raise ValueError("Bucharest does not start on day 13 as required.")

# Ensure Lyon starts on day 7
if cities["Lyon"]["start"] != 7:
    raise ValueError("Lyon does not start on day 7 as required.")

# Output the JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))