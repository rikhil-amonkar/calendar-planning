import json

def generate_itinerary():
    # Define the itinerary based on the reasoning above
    itinerary = [
        {"day_range": "Day 1-2", "place": "Prague"},
        {"day_range": "Day 3-7", "place": "Tallinn"},
        {"day_range": "Day 8-10", "place": "Berlin"},
        {"day_range": "Day 11-12", "place": "Tallinn"}
    ]
    
    # Convert the itinerary to JSON format
    itinerary_json = {"itinerary": itinerary}
    
    return itinerary_json

# Generate and print the itinerary
itinerary_output = generate_itinerary()
print(json.dumps(itinerary_output, indent=4))