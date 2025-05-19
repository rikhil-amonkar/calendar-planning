import json

# Define the parameters of the trip
cities_duration = {
    "Brussels": 3,
    "Helsinki": 3,
    "Split": 4,
    "Dubrovnik": 2,
    "Istanbul": 5,  # Days 1-5 are booked for the show
    "Milan": 4,
    "Vilnius": 5,   # Workshop days include Days 18-22
    "Frankfurt": 3  # Wedding days are 16-18
}

# Define direct flight connections
direct_flights = {
    "Milan": ["Frankfurt", "Split", "Vilnius", "Helsinki"],
    "Frankfurt": ["Milan", "Split", "Vilnius"],
    "Split": ["Frankfurt", "Vilnius", "Milan", "Dubrovnik", "Helsinki"],
    "Dubrovnik": ["Istanbul", "Split", "Frankfurt"],
    "Istanbul": ["Brussels", "Helsinki", "Milan", "Vilnius", "Frankfurt"],
    "Brussels": ["Vilnius", "Helsinki", "Istanbul", "Milan", "Frankfurt"],
    "Helsinki": ["Brussels", "Istanbul", "Vilnius", "Dubrovnik", "Split"],
    "Vilnius": ["Brussels", "Istanbul", "Milan", "Frankfurt", "Helsinki"],
}

# Compute the itinerary based on constraints and direct flights
 itinerary = []
 
total_days = 22
current_day = 1

# Attend show in Istanbul first
itinerary.append({"day_range": f"Day {current_day}-{current_day + 4}", "place": "Istanbul"}) 
current_day += 5

# Visit Brussels
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Istanbul", "to": "Brussels"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + 2}", "place": "Brussels"})
current_day += 3

# Visit Helsinki
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Brussels", "to": "Helsinki"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + 2}", "place": "Helsinki"})
current_day += 3

# Visit Split
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Helsinki", "to": "Split"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + 3}", "place": "Split"})
current_day += 4

# Visit Dubrovnik
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Split", "to": "Dubrovnik"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + 1}", "place": "Dubrovnik"})
current_day += 2

# Back to Split, to fly to Milan
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Dubrovnik", "to": "Split"})
current_day += 1

itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Split", "to": "Milan"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + 3}", "place": "Milan"})
current_day += 4

# Go to Frankfurt for wedding
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Milan", "to": "Frankfurt"})
itinerary.append({"day_range": f"Day {current_day}-{current_day + 2}", "place": "Frankfurt"})
current_day += 3

# Visit Vilnius for workshop
itinerary.append({"flying": f"Day {current_day}-{current_day}", "from": "Frankfurt", "to": "Vilnius"})
itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": "Vilnius"}) 

# Convert to JSON format
output = json.dumps(itinerary, indent=4)
print(output)