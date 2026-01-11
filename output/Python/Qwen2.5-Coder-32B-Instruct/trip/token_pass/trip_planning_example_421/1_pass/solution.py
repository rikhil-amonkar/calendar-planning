import json

def create_itinerary():
    # Define the fixed stays
    itinerary = [
        {"day_range": "Day 1-5", "place": "Nice"},
        {"day_range": "Day 5-6", "place": "Frankfurt"},
        {"day_range": "Day 6-12", "place": "Krakow"},
        {"day_range": "Day 12-19", "place": "Dublin"},
        {"day_range": "Day 19-20", "place": "Frankfurt"}
    ]
    
    return {"itinerary": itinerary}

# Generate the itinerary
result = create_itinerary()

# Print the result as JSON
print(json.dumps(result, indent=4))