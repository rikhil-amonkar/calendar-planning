import json

# Define input parameters
start_city = "Prague"
end_city = "Stockholm"
stay_prague_days = 2
stay_berlin_days = 3
stay_tallinn_days = 5
stay_stockholm_days = 5

conference_berlin_start_day = 6
conference_berlin_end_day = 8
relative_meeting_tallinn_start_day = 8
relative_meeting_tallinn_end_day = 12

# Create a dictionary to hold the flight information and cities
flight_data = {
    "flights": [],
    "cities": []
}

# Initialize the itinerary with the starting city
flight_data["cities"].append({
    "place": start_city,
    "day_range": f"Day 1-{1 + stay_prague_days - 1}"
})

# Determine the optimal flight routes based on constraints
# From Prague to Berlin on day 2
flight_data["flights"].append({
    "flying": "Day 2-2",
    "from": "Prague",
    "to": "Berlin"
})
flight_data["cities"].append({
    "place": "Berlin",
    "day_range": f"Day 3-{3 + stay_berlin_days - 1}"
})

# From Berlin to Tallinn on day 6
flight_data["flights"].append({
    "flying": "Day 6-6",
    "from": "Berlin",
    "to": "Tallinn"
})
flight_data["cities"].append({
    "place": "Tallinn",
    "day_range": f"Day 7-{7 + stay_tallinn_days - 1}"
})

# From Tallinn to Stockholm on day 12
flight_data["flights"].append({
    "flying": "Day 12-12",
    "from": "Tallinn",
    "to": "Stockholm"
})
flight_data["cities"].append({
    "place": "Stockholm",
    "day_range": f"Day 13-{13 + stay_stockholm_days - 1}"
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