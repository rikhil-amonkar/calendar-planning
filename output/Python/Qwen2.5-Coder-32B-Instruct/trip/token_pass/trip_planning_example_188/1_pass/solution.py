import json

def calculate_itinerary():
    # Define the constraints
    brussels_days = 2
    split_days = 5
    barcelona_days = 7
    total_days = 12
    
    # Initialize the itinerary list
    itinerary = []
    
    # Brussels stay (Days 1-2)
    itinerary.append({"day_range": f"Day 1-{brussels_days}", "place": "Brussels"})
    
    # Travel from Brussels to Barcelona on Day 2
    # This means Day 2 is counted for both cities
    days_in_barcelona = barcelona_days - 1  # Subtract 1 because Day 2 is shared
    start_day_barcelona = brussels_days
    end_day_barcelona = start_day_barcelona + days_in_barcelona
    
    # Barcelona stay (Days 2-8)
    itinerary.append({"day_range": f"Day {start_day_barcelona}-{end_day_barcelona}", "place": "Barcelona"})
    
    # Travel from Barcelona to Split on Day 8
    # This means Day 8 is counted for both cities
    days_in_split = split_days - 1  # Subtract 1 because Day 8 is shared
    start_day_split = end_day_barcelona
    end_day_split = start_day_split + days_in_split
    
    # Split stay (Days 8-13)
    itinerary.append({"day_range": f"Day {start_day_split}-{end_day_split}", "place": "Split"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Calculate and print the itinerary
itinerary_json = calculate_itinerary()
print(json.dumps(itinerary_json, indent=4))