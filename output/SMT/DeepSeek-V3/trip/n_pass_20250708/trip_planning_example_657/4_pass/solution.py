def create_itinerary():
    # Define the itinerary day by day
    itinerary = [
        {"day_range": "Day 1-4", "place": "Valencia"},
        {"day_range": "Day 4", "place": "Valencia"},
        {"day_range": "Day 4", "place": "Frankfurt"},
        {"day_range": "Day 5-7", "place": "Frankfurt"},
        {"day_range": "Day 7", "place": "Frankfurt"},
        {"day_range": "Day 7", "place": "Manchester"},
        {"day_range": "Day 8-11", "place": "Manchester"},
        {"day_range": "Day 11", "place": "Manchester"},
        {"day_range": "Day 11", "place": "Oslo"},
        {"day_range": "Day 12", "place": "Oslo"},
        {"day_range": "Day 12", "place": "Vilnius"},
        {"day_range": "Day 13-16", "place": "Frankfurt"}
    ]
    
    # Verify flight connections exist
    flight_connections = {
        "Valencia": ["Frankfurt", "Naples"],
        "Manchester": ["Frankfurt", "Naples", "Oslo"],
        "Naples": ["Manchester", "Frankfurt", "Oslo", "Valencia"],
        "Oslo": ["Naples", "Frankfurt", "Vilnius", "Manchester"],
        "Vilnius": ["Frankfurt", "Oslo"],
        "Frankfurt": ["Valencia", "Manchester", "Naples", "Oslo", "Vilnius"]
    }
    
    # Verify day counts
    day_counts = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 0,
        "Oslo": 2,
        "Vilnius": 1
    }
    
    # Calculate actual day counts
    actual_counts = {city: 0 for city in day_counts}
    for entry in itinerary:
        if '-' in entry["day_range"]:
            start, end = map(int, entry["day_range"].split(' ')[1].split('-'))
            days = end - start + 1
        else:
            days = 1
        actual_counts[entry["place"]] += days
    
    # Check if counts match
    for city in day_counts:
        if actual_counts[city] != day_counts[city]:
            return {"error": f"Day count mismatch for {city}"}
    
    # Check flight connections
    for i in range(len(itinerary)-1):
        if '-' in itinerary[i]["day_range"] and '-' in itinerary[i+1]["day_range"]:
            continue  # Not a flight day
        from_city = itinerary[i]["place"]
        to_city = itinerary[i+1]["place"]
        if from_city != to_city and to_city not in flight_connections[from_city]:
            return {"error": f"No flight connection from {from_city} to {to_city}"}
    
    return {"itinerary": itinerary}

# Generate the itinerary
itinerary = create_itinerary()
print(itinerary)