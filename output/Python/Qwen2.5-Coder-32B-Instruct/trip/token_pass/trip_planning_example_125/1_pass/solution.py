import json

def calculate_itinerary():
    # Define the constraints
    stuttgart_days = 6
    seville_days = 7
    manchester_days = 4
    total_days = 15
    
    # Initialize the itinerary list
    itinerary = []
    
    # Day 1 to Day 6: Stay in Stuttgart
    itinerary.append({"day_range": f"Day 1-{stuttgart_days}", "place": "Stuttgart"})
    
    # Day 6 to Day 8: Transition from Stuttgart to Manchester (Day 6 counts in both)
    # We need to stay in Manchester for 4 days total, so we stay 2 more days after transitioning
    itinerary.append({"day_range": f"Day {stuttgart_days}-{stuttgart_days + manchester_days - 1}", "place": "Manchester"})
    
    # Day 8 to Day 14: Transition from Manchester to Seville (Day 8 counts in both)
    # We need to stay in Seville for 7 days
    itinerary.append({"day_range": f"Day {stuttgart_days + manchester_days - 1}-{total_days}", "place": "Seville"})
    
    # Output the itinerary as a JSON object
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())