import json

def generate_itinerary():
    # Define the itinerary based on the calculated plan
    itinerary = [
        {"day_range": "Day 1-4", "place": "Vilnius"},
        {"day_range": "Day 5-9", "place": "Split"},
        {"day_range": "Day 10-11", "place": "Madrid"},
        {"day_range": "Day 12-14", "place": "Santorini"}
    ]
    
    # Convert the itinerary to JSON format
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())