def solve_itinerary():
    # Cities and their required days
    cities = {
        "Istanbul": 2,
        "Rome": 3,
        "Seville": 4,
        "Naples": 7,
        "Santorini": 4
    }
    
    # Direct flights
    direct_flights = {
        "Rome": ["Santorini", "Seville", "Naples", "Istanbul"],
        "Santorini": ["Rome", "Naples"],
        "Seville": ["Rome"],
        "Naples": ["Istanbul", "Santorini", "Rome"],
        "Istanbul": ["Naples", "Rome"]
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Assign Santorini for wedding (days 13-16)
    for day in range(13, 17):
        itinerary.append({"day_range": f"Day {day}", "place": "Santorini"})
    
    # Assign Istanbul for relatives (day 6 or 7)
    # Let's choose day 6
    itinerary.append({"day_range": "Day 6", "place": "Istanbul"})
    itinerary.append({"day_range": "Day 7", "place": "Istanbul"})
    
    # Remaining days to allocate: 1-5, 8-12
    # We need:
    # Rome: 3 days
    # Seville: 4 days
    # Naples: 7 days (but we've already allocated some days)
    
    # Calculate remaining days needed
    remaining_days = {
        "Rome": 3,
        "Seville": 4,
        "Naples": 7,
        "Istanbul": 0,  # already allocated 2 days
        "Santorini": 0  # already allocated 4 days
    }
    
    # Allocate remaining days respecting flight connections
    # Start with Rome (connected to most cities)
    itinerary.append({"day_range": "Day 1", "place": "Rome"})
    itinerary.append({"day_range": "Day 2", "place": "Rome"})
    itinerary.append({"day_range": "Day 3", "place": "Rome"})
    
    # From Rome, fly to Seville
    itinerary.append({"day_range": "Day 4", "place": "Rome"})
    itinerary.append({"day_range": "Day 4", "place": "Seville"})
    itinerary.append({"day_range": "Day 5", "place": "Seville"})
    itinerary.append({"day_range": "Day 8", "place": "Seville"})
    itinerary.append({"day_range": "Day 9", "place": "Seville"})
    
    # From Seville, fly back to Rome
    itinerary.append({"day_range": "Day 10", "place": "Seville"})
    itinerary.append({"day_range": "Day 10", "place": "Rome"})
    
    # From Rome, fly to Naples
    itinerary.append({"day_range": "Day 11", "place": "Rome"})
    itinerary.append({"day_range": "Day 11", "place": "Naples"})
    itinerary.append({"day_range": "Day 12", "place": "Naples"})
    
    # From Naples, fly to Istanbul on day 6
    itinerary.append({"day_range": "Day 6", "place": "Naples"})
    itinerary.append({"day_range": "Day 6", "place": "Istanbul"})
    
    # From Istanbul, fly back to Naples
    itinerary.append({"day_range": "Day 7", "place": "Istanbul"})
    itinerary.append({"day_range": "Day 7", "place": "Naples"})
    
    # From Naples, fly to Santorini on day 13
    itinerary.append({"day_range": "Day 13", "place": "Naples"})
    itinerary.append({"day_range": "Day 13", "place": "Santorini"})
    
    # Verify all constraints are met
    days_count = {city: 0 for city in cities}
    for entry in itinerary:
        if '-' in entry["day_range"]:
            start, end = map(int, entry["day_range"].replace("Day ", "").split('-'))
            days = end - start + 1
        else:
            days = 1
        days_count[entry["place"]] += days
    
    for city, required in cities.items():
        if days_count[city] != required:
            return {"error": f"Constraint not met for {city}: expected {required}, got {days_count[city]}"}
    
    # Check flight connections
    prev_city = None
    for entry in itinerary:
        current_city = entry["place"]
        if prev_city and prev_city != current_city:
            if current_city not in direct_flights[prev_city]:
                return {"error": f"No direct flight from {prev_city} to {current_city}"}
        prev_city = current_city
    
    return {"itinerary": itinerary}

# Execute the function
result = solve_itinerary()
print(result)