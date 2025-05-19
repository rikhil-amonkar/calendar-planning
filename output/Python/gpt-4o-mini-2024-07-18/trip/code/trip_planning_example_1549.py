import json

# Define the trip constraints
city_stays = {
    "Prague": 5,
    "Tallinn": 3,
    "Warsaw": 2,
    "Porto": 3,
    "Naples": 5,
    "Milan": 3,
    "Lisbon": 5,
    "Santorini": 5,
    "Riga": 4,
    "Stockholm": 2,
}

# Add specific constraints
constraints = {
    "Tallinn": {"days": [18, 19, 20]},  # visit relatives in Tallinn
    "Milan": {"days": [24, 25, 26]},     # meet friend in Milan
}

# Define the direct flight connections
direct_flights = {
    "Riga": ["Prague", "Tallinn", "Milan", "Warsaw", "Stockholm"],
    "Prague": ["Riga", "Milan", "Tallinn"],
    "Tallinn": ["Riga", "Warsaw"],
    "Warsaw": ["Naples", "Lisbon", "Milan", "Tallinn", "Prague", "Porto"],
    "Porto": ["Lisbon", "Milan", "Warsaw"],
    "Milan": ["Prague", "Naples", "Porto", "Warsaw", "Santorini", "Stockholm"],
    "Lisbon": ["Porto", "Warsaw", "Milan", "Riga", "Prague"],
    "Naples": ["Warsaw", "Milan", "Santorini"],
    "Santorini": ["Milan", "Stockholm"],
    "Stockholm": ["Riga", "Milan", "Lisbon"],
}

# Plan days for the trip
def plan_trip():
    itinerary = []
    current_day = 1
    city_sequence = [
        ("Prague", 5),
        ("Riga", 4),
        ("Tallinn", 3),
        ("Warsaw", 2),
        ("Milan", 3),
        ("Lisbon", 5),
        ("Porto", 3),
        ("Naples", 5),
        ("Santorini", 5),
        ("Stockholm", 2),
    ]

    for city, duration in city_sequence:
        # Handle specific constraints
        if city == "Tallinn" and (current_day + duration > 20):
            continue # Skip to Tallinn when days exceed day 20
        
        # Adjust days for visiting relatives or friends
        if city == "Tallinn" and current_day == 18:
            itinerary.append({"day_range": f"Day {current_day}-{current_day+duration-1}", "place": city})
            current_day += duration
            continue
        
        if city == "Milan" and current_day == 24:
            itinerary.append({"day_range": f"Day {current_day}-{current_day+duration-1}", "place": city})
            current_day += duration
            continue
            
        # Add city stay to itinerary
        if current_day + duration <= 29:  # ensure we do not exceed 28 days
            itinerary.append({"day_range": f"Day {current_day}-{current_day+duration-1}", "place": city})
            current_day += duration
            
            # Add direct flight transition only if it's not the end of the trip
            if current_day <= 28:
                next_city = city_sequence[city_sequence.index((city, duration)) + 1][0]
                itinerary.append({
                    "flying": f"Day {current_day-1}-{current_day-1}",
                    "from": city,
                    "to": next_city
                }) 
                current_day += 1  # increment for travel day
            
    return itinerary

# Run the trip planning logic
trip_plan = plan_trip()

# Output the result as a JSON-formatted dictionary
print(json.dumps(trip_plan, indent=4))