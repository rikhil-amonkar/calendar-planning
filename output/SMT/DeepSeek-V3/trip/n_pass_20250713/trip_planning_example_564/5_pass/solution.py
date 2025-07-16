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
    
    # Assign Istanbul for relatives (days 6-7)
    itinerary.append({"day_range": "Day 6", "place": "Istanbul"})
    itinerary.append({"day_range": "Day 7", "place": "Istanbul"})
    
    # Allocate remaining days
    # Days 1-5: Start in Rome (3 days), then Seville (2 days)
    itinerary.append({"day_range": "Day 1", "place": "Rome"})
    itinerary.append({"day_range": "Day 2", "place": "Rome"})
    itinerary.append({"day_range": "Day 3", "place": "Rome"})
    
    # Fly to Seville on day 4
    itinerary.append({"day_range": "Day 4", "place": "Rome"})
    itinerary.append({"day_range": "Day 4", "place": "Seville"})
    itinerary.append({"day_range": "Day 5", "place": "Seville"})
    
    # Days 8-12: Continue in Seville, then Naples
    itinerary.append({"day_range": "Day 8", "place": "Seville"})
    itinerary.append({"day_range": "Day 9", "place": "Seville"})
    
    # Fly to Naples on day 10
    itinerary.append({"day_range": "Day 10", "place": "Seville"})
    itinerary.append({"day_range": "Day 10", "place": "Rome"})
    itinerary.append({"day_range": "Day 10", "place": "Naples"})
    
    # Stay in Naples until day 12
    itinerary.append({"day_range": "Day 11", "place": "Naples"})
    itinerary.append({"day_range": "Day 12", "place": "Naples"})
    
    # Fly to Istanbul on day 6
    itinerary.append({"day_range": "Day 6", "place": "Naples"})
    itinerary.append({"day_range": "Day 6", "place": "Istanbul"})
    
    # Fly back to Naples on day 7
    itinerary.append({"day_range": "Day 7", "place": "Istanbul"})
    itinerary.append({"day_range": "Day 7", "place": "Naples"})
    
    # Fly to Santorini on day 13
    itinerary.append({"day_range": "Day 13", "place": "Naples"})
    itinerary.append({"day_range": "Day 13", "place": "Santorini"})
    
    # Verify all constraints
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
    
    # Final itinerary with proper day ranges
    final_itinerary = []
    current_place = None
    start_day = None
    
    for day in range(1, 17):
        place = None
        for entry in itinerary:
            if entry["day_range"] == f"Day {day}" or (day == int(entry["day_range"].split('-')[0].replace("Day ", "")) if '-' in entry["day_range"] else False:
                place = entry["place"]
                break
        
        if place != current_place:
            if current_place is not None:
                if start_day == day - 1:
                    final_itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    final_itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_place})
            current_place = place
            start_day = day
    
    # Add last stay
    if start_day == 16:
        final_itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
    else:
        final_itinerary.append({"day_range": f"Day {start_day}-16", "place": current_place})
    
    return {"itinerary": final_itinerary}

# Execute the function
result = solve_itinerary()
print(result)