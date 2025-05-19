import json

# Defining the trip constraints
trip_days = 18
stay_durations = {
    "Helsinki": 4,
    "Valencia": 5,
    "Dubrovnik": 4,
    "Porto": 3,
    "Prague": 3,
    "Reykjavik": 4
}

# Total days check
if sum(stay_durations.values()) != trip_days:
    raise ValueError("Stay durations do not sum up to the total trip days.")

# Direct flights available
direct_flights = {
    "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
    "Prague": ["Helsinki", "Valencia"],
    "Valencia": ["Prague", "Porto"],
    "Dubrovnik": ["Helsinki"],
    "Porto": ["Valencia"],
    "Reykjavik": ["Helsinki", "Prague"]
}

# Itinerary computation
itinerary = []
current_day = 1

# Helsinki stay
itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_durations['Helsinki'] - 1}", "place": "Helsinki"})
current_day += stay_durations['Helsinki']

# Prague stay
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Helsinki", "to": "Prague"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_durations['Prague'] - 1}", "place": "Prague"})
current_day += stay_durations['Prague']

# Valencia stay
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Prague", "to": "Valencia"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_durations['Valencia'] - 1}", "place": "Valencia"})
current_day += stay_durations['Valencia']

# Porto stay (to coincide with meeting friend at the end)
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Valencia", "to": "Porto"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_durations['Porto'] - 1}", "place": "Porto"})
current_day += stay_durations['Porto']

# Reykjavik stay
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Porto", "to": "Reykjavik"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_durations['Reykjavik'] - 1}", "place": "Reykjavik"})
current_day += stay_durations['Reykjavik']

# Dubrovnik stay
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Reykjavik", "to": "Dubrovnik"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_durations['Dubrovnik'] - 1}", "place": "Dubrovnik"})
current_day += stay_durations['Dubrovnik']

# Convert itinerary to JSON format
itinerary_json = json.dumps(itinerary, indent=4)

# Output the result
print(itinerary_json)