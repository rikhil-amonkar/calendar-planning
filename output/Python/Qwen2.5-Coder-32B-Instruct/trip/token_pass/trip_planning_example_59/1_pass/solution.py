import json

def generate_itinerary():
    # Define the fixed stays and constraints
    total_days = 16
    bucharest_days = 7
    lyon_days = 7
    porto_days = 4
    
    # Initialize the itinerary list
    itinerary = []
    
    # Day 1-7 in Bucharest (inclusive of transition day)
    itinerary.append({"day_range": "Day 1-7", "place": "Bucharest"})
    
    # Transition to Lyon on Day 7, so Day 7 counts in both Bucharest and Lyon
    # No additional stay in Lyon needed beyond Day 7
    
    # Transition to Porto on Day 8
    itinerary.append({"day_range": "Day 8-12", "place": "Porto"})
    
    # Transition back to Lyon on Day 12
    # Stay in Lyon for the remaining days (Day 13-16)
    itinerary.append({"day_range": "Day 13-16", "place": "Lyon"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())