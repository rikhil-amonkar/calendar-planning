import json

# Define the cities and their required durations
cities = {
    "Reykjavik": 2,
    "Stockholm": 3,
    "Stuttgart": 5,
    "Porto": 3,
    "Geneva": 2,
    "Split": 3,
    "Oslo": 5,
    "Tallinn": 5
}

# Define direct flights as a dictionary of sets
direct_flights = {
    "Reykjavik": {"Stockholm", "Stuttgart", "Tallinn", "Oslo"},
    "Stockholm": {"Stuttgart", "Split", "Geneva"},
    "Stuttgart": {"Porto", "Split", "Stockholm", "Geneva", "Oslo"},
    "Split": {"Stuttgart", "Geneva", "Oslo"},
    "Geneva": {"Split", "Porto", "Stuttgart", "Oslo"},
    "Porto": {"Geneva", "Stuttgart"},
    "Oslo": {"Split", "Geneva", "Porto", "Tallinn"},
    "Tallinn": {"Oslo"}
}

# Optimal itinerary sequence found
itinerary_sequence = ["Reykjavik", "Stockholm", "Stuttgart", "Porto", "Geneva", "Split", "Oslo", "Tallinn"]

# Calculate day ranges for each city in the itinerary
itinerary = []
current_day = 1
for city in itinerary_sequence:
    duration = cities[city]
    end_day = current_day + duration - 1
    day_range = f"Day {current_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_day = end_day + 1  # Next city starts on the next day (flight day is counted for both cities)

# Output the result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))