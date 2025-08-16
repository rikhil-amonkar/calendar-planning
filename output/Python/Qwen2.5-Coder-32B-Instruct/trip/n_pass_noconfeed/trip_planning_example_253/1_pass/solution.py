import json

def calculate_itinerary():
    # Define the constraints
    total_days = 14
    amsterdam_stay = 3
    vienna_stay = 7
    santorini_stay = 4
    lyon_stay = 3
    amsterdam_workshop_days = range(9, 12)  # Day 9 to Day 11
    lyon_wedding_days = range(7, 10)        # Day 7 to Day 9
    
    # Initialize the itinerary
    itinerary = []
    
    # Start with Vienna since it has the longest stay
    start_day = 1
    end_day = start_day + vienna_stay - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Vienna"})
    
    # Next, go to Santorini (must be before Amsterdam due to flight constraints)
    start_day = end_day + 1
    end_day = start_day + santorini_stay - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Santorini"})
    
    # Then, go to Amsterdam (workshop days are Day 9-11)
    start_day = max(end_day + 1, 9)  # Ensure we are in Amsterdam for the workshop
    end_day = start_day + amsterdam_stay - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Amsterdam"})
    
    # Finally, go to Lyon (wedding days are Day 7-9, but we need to adjust for overlaps)
    start_day = max(end_day + 1, 7)  # Ensure we are in Lyon for the wedding
    end_day = start_day + lyon_stay - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Lyon"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output))