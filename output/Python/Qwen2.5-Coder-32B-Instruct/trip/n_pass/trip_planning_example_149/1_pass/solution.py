import json

def calculate_itinerary():
    # Input variables
    total_days = 10
    london_stay = 3
    santorini_stay = 6
    istanbul_stay = 3
    conference_days = [5, 10]
    
    # Initialize itinerary list
    itinerary = []
    
    # Day 1 to 3: London
    itinerary.append({"day_range": f"Day 1-{london_stay}", "place": "London"})
    
    # Day 4: Travel day (London to Santorini)
    current_day = london_stay + 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Travel (London to Santorini)"})
    
    # Day 5: Santorini (Conference Day)
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Santorini"})
    
    # Day 6 to 9: Santorini
    current_day += 1
    santorini_end = current_day + santorini_stay - 3  # Subtracting the conference days already counted
    itinerary.append({"day_range": f"Day {current_day}-{santorini_end}", "place": "Santorini"})
    current_day = santorini_end + 1
    
    # Day 10: Santorini (Conference Day)
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Santorini"})
    
    # Day 11: Travel day (Santorini to Istanbul)
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Travel (Santorini to Istanbul)"})
    
    # Day 12 to 14: Istanbul
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + istanbul_stay - 1}", "place": "Istanbul"})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())