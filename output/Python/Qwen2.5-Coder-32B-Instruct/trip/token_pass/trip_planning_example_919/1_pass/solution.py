import json

def generate_itinerary():
    # Define the itinerary based on the constraints and transitions
    itinerary = [
        {"day_range": "Day 1-4", "place": "Vienna"},
        {"day_range": "Day 5-6", "place": "Milan"},
        {"day_range": "Day 7-9", "place": "Rome"},
        {"day_range": "Day 10-11", "place": "Riga"},
        {"day_range": "Day 11-13", "place": "Lisbon"},
        {"day_range": "Day 13-14", "place": "Vilnius"},
        {"day_range": "Day 13-15", "place": "Oslo"}
    ]
    
    # Convert the itinerary to JSON format
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())