import json

def generate_itinerary():
    # Define the constraints
    total_days = 12
    stay_riga = 5
    stay_vilnius = 7
    stay_dublin = 2
    
    # Initialize the itinerary list
    itinerary = []
    
    # Day 1-2: Dublin
    itinerary.append({"day_range": "Day 1-2", "place": "Dublin"})
    
    # Day 3: Flight from Dublin to Riga
    # Day 3-7: Stay in Riga (including arrival day)
    itinerary.append({"day_range": "Day 3-7", "place": "Riga"})
    
    # Day 8: Flight from Riga to Vilnius
    # Day 8-14: Stay in Vilnius (including arrival day)
    itinerary.append({"day_range": "Day 8-14", "place": "Vilnius"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = generate_itinerary()
print(json.dumps(itinerary_json, indent=4))