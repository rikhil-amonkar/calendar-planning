import json

def generate_itinerary():
    # Define the constraints
    total_days = 17
    naples_stay = 5
    vienna_stay = 7
    vilnius_stay = 7
    
    # Initialize the itinerary list
    itinerary = []
    
    # Day 1-5: Naples
    itinerary.append({"day_range": "Day 1-5", "place": "Naples"})
    
    # Day 6-12: Vienna
    itinerary.append({"day_range": "Day 6-12", "place": "Vienna"})
    
    # Day 12-17: Vilnius
    itinerary.append({"day_range": "Day 12-17", "place": "Vilnius"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = generate_itinerary()
print(json.dumps(itinerary_json, indent=4))