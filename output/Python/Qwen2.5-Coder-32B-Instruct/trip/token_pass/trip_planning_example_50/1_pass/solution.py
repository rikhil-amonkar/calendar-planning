import json

def calculate_itinerary():
    # Define the number of days to stay in each city
    days_in_vilnius = 4
    days_in_munich = 3
    days_in_mykonos = 7
    
    # Initialize the itinerary list
    itinerary = []
    
    # Day 1-4: Vilnius
    itinerary.append({"day_range": "Day 1-4", "place": "Vilnius"})
    
    # Day 5: Vilnius to Munich (transition day)
    # This day is counted as part of Vilnius' stay
    # No new entry needed as it's already included in Day 1-4
    
    # Day 6-7: Munich
    # Since Day 5 was counted as Vilnius, we only need 2 more days in Munich
    itinerary.append({"day_range": "Day 5-7", "place": "Munich"})
    
    # Day 8: Munich to Mykonos (transition day)
    # This day is counted as part of Munich's stay
    # No new entry needed as it's already included in Day 5-7
    
    # Day 9-14: Mykonos
    # Since Day 8 was counted as Munich, we need 6 more days in Mykonos
    itinerary.append({"day_range": "Day 8-14", "place": "Mykonos"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Calculate and print the itinerary
itinerary_json = calculate_itinerary()
print(json.dumps(itinerary_json, indent=4))