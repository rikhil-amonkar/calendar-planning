import json

# Define input parameters
start_city = "Split"
end_city = "London"
stay_split_days = 6
stay_santorini_days = 7
stay_london_days = 7

conference_santorini_day = 12

# Create a dictionary to hold the flight information and cities
flight_data = {
    "flights": [],
    "cities": []
}

# Initialize the itinerary with the starting city
flight_data["cities"].append({
    "place": start_city,
    "day_range": f"Day 1-{1 + stay_split_days - 1}"
})

# Determine the optimal flight routes based on constraints
# From Split to Santorini on day 6
flight_data["flights"].append({
    "flying": "Day 6-6",
    "from": "Split",
    "to": "Santorini"
})
flight_data["cities"].append({
    "place": "Santorini",
    "day_range": f"Day 7-{7 + stay_santorini_days - 1}"
})

# From Santorini to London on day 12
flight_data["flights"].append({
    "flying": "Day 12-12",
    "from": "Santorini",
    "to": "London"
})
flight_data["cities"].append({
    "place": "London",
    "day_range": f"Day 13-{13 + stay_london_days - 1}"
})

# Convert the data to the required JSON format
output = []
for city in flight_data["cities"]:
    output.append({
        "day_range": city["day_range"],
        "place": city["place"]
    })
for flight in flight_data["flights"]:
    output.append({
        "flying": flight["flying"],
        "from": flight["from"],
        "to": flight["to"]
    })

# Print the JSON output
print(json.dumps(output))