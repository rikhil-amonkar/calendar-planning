import json

def calculate_itinerary():
    # Input variables
    total_days = 10
    london_stay = 3
    santorini_stay = 3
    istanbul_stay = 2
    
    # Initialize itinerary list
    itinerary = []
    
    # Day 1 to 3: London
    start_day = 1
    end_day = start_day + london_stay - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "London"})
    
    # Day 4: Travel day (London to Santorini)
    start_day = end_day + 1
    end_day = start_day
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Travel (London to Santorini)"})
    
    # Day 5 to 7: Santorini
    start_day = end_day + 1
    end_day = start_day + santorini_stay - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Santorini"})
    
    # Day 8: Travel day (Santorini to Istanbul)
    start_day = end_day + 1
    end_day = start_day
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Travel (Santorini to Istanbul)"})
    
    # Day 9 to 10: Istanbul
    start_day = end_day + 1
    end_day = start_day + istanbul_stay - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Istanbul"})
    
    # Ensure the total number of days matches the specified total days
    if end_day != total_days:
        raise ValueError(f"The itinerary does not cover the total number of days ({total_days}). It ends on Day {end_day}.")
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())