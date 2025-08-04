import json

def calculate_itinerary():
    # Input constraints
    total_days = 10
    london_stay = 3
    santorini_stay = 6
    istanbul_stay = 3
    conference_days = [5, 10]
    
    # Initialize itinerary list
    itinerary = []
    
    # Day 1-3: London (3 days)
    itinerary.append({"day_range": f"Day 1-{london_stay}", "place": "London"})
    
    # Day 4: Travel from London to Santorini
    current_day = london_stay + 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Travel (London to Santorini)"})
    
    # Day 5: Santorini (Conference Day 1)
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Santorini"})
    current_day += 1
    
    # Day 6-9: Santorini (4 days)
    santorini_end_day = current_day + santorini_stay - 3  # 3 days already spent including conference day
    itinerary.append({"day_range": f"Day {current_day}-{santorini_end_day - 1}", "place": "Santorini"})
    current_day = santorini_end_day
    
    # Day 10: Santorini (Conference Day 2)
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Santorini"})
    current_day += 1
    
    # Day 11: Travel from Santorini to Istanbul
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Travel (Santorini to Istanbul)"})
    current_day += 1
    
    # Day 12-14: Istanbul (3 days)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + istanbul_stay - 1}", "place": "Istanbul"})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())