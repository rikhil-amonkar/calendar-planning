def create_itinerary():
    # Define the itinerary day by day with proper flight days
    itinerary = [
        {"day_range": "Day 1-4", "place": "Valencia"},
        {"day_range": "Day 4", "place": "Valencia"},
        {"day_range": "Day 4", "place": "Naples"},
        {"day_range": "Day 5-8", "place": "Naples"},
        {"day_range": "Day 8", "place": "Naples"},
        {"day_range": "Day 8", "place": "Oslo"},
        {"day_range": "Day 9-11", "place": "Oslo"},
        {"day_range": "Day 11", "place": "Oslo"},
        {"day_range": "Day 11", "place": "Vilnius"},
        {"day_range": "Day 12", "place": "Vilnius"},
        {"day_range": "Day 12", "place": "Frankfurt"},
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
    
    # Expected day counts
    expected_counts = {
        "Frankfurt": 4,
        "Manchester": 0,  # Not visiting Manchester in this itinerary
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2
    }
    
    # Calculate actual day counts
    actual_counts = {city: 0 for city in expected_counts}
    for entry in itinerary:
        if '-' in entry["day_range"]:
            start, end = map(int, entry["day_range"].split(' ')[1].split('-'))
            days = end - start + 1
        else:
            days = 1
        actual_counts[entry["place"]] += days
    
    # Verify day counts match
    for city in expected_counts:
        if actual_counts[city] != expected_counts[city]:
            return {"error": f"Day count mismatch for {city}: expected {expected_counts[city]}, got {actual_counts[city]}"}
    
    # Verify flight connections
    for i in range(len(itinerary)-1):
        current = itinerary[i]
        next_entry = itinerary[i+1]
        
        # Skip if not a transition day
        if '-' in current["day_range"] and '-' in next_entry["day_range"]:
            continue
        
        from_city = current["place"]
        to_city = next_entry["place"]
        
        if from_city != to_city and to_city not in flight_connections[from_city]:
            return {"error": f"No flight connection from {from_city} to {to_city}"}
    
    return {"itinerary": itinerary}

# Generate the itinerary
itinerary = create_itinerary()
print(itinerary)