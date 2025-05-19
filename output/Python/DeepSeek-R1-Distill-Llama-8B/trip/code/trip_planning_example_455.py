import json

# Define input parameters
start_city = "Reykjavik"
end_city = "Krakow"
stay_reykjavik_days = 7
stay_riga_days = 2
stay_warsaw_days = 3
stay_istanbul_days = 6
stay_krakow_days = 7

friend_meeting_riga_start_day = 8
friend_meeting_riga_end_day = 9
wedding_istanbul_start_day = 2
wedding_istanbul_end_day = 7

# Create a dictionary to hold the flight information and cities
flight_data = {
    "flights": [],
    "cities": []
}

# Initialize the itinerary with the starting city
flight_data["cities"].append({
    "place": start_city,
    "day_range": f"Day 1-{1 + stay_reykjavik_days - 1}"
})

# Determine the optimal flight routes based on constraints
# From Reykjavik to Riga on day 7
flight_data["flights"].append({
    "flying": "Day 7-7",
    "from": "Reykjavik",
    "to": "Riga"
})
flight_data["cities"].append({
    "place": "Riga",
    "day_range": f"Day {friend_meeting_riga_start_day}-{friend_meeting_riga_end_day}"
})

# From Riga to Warsaw on day 9
flight_data["flights"].append({
    "flying": "Day 9-9",
    "from": "Riga",
    "to": "Warsaw"
})
flight_data["cities"].append({
    "place": "Warsaw",
    "day_range": f"Day 10-{10 + stay_warsaw_days - 1}"
})

# From Warsaw to Istanbul on day 12
flight_data["flights"].append({
    "flying": "Day 12-12",
    "from": "Warsaw",
    "to": "Istanbul"
})
flight_data["cities"].append({
    "place": "Istanbul",
    "day_range": f"Day 13-{13 + stay_istanbul_days - 1}"
})

# From Istanbul to Krakow on day 18
flight_data["flights"].append({
    "flying": "Day 18-18",
    "from": "Istanbul",
    "to": "Krakow"
})
flight_data["cities"].append({
    "place": "Krakow",
    "day_range": f"Day 19-{19 + stay_krakow_days - 1}"
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