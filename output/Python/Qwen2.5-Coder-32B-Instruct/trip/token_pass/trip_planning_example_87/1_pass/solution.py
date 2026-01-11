import json

def generate_itinerary():
    # Define the constraints
    total_days = 7
    days_in_riga = 2
    days_in_amsterdam = 2
    days_in_mykonos = 5
    
    # Initialize the itinerary list
    itinerary = []
    
    # Add Riga to the itinerary
    itinerary.append({"day_range": "Day 1-2", "place": "Riga"})
    
    # Add Amsterdam to the itinerary
    itinerary.append({"day_range": "Day 2-4", "place": "Amsterdam"})
    
    # Add Mykonos to the itinerary
    itinerary.append({"day_range": "Day 4-7", "place": "Mykonos"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = generate_itinerary()
print(json.dumps(itinerary_json, indent=4))