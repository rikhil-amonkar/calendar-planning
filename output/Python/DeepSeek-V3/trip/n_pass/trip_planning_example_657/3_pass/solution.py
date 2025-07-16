import json

def generate_itinerary():
    # Revised itinerary with better geographical flow
    itinerary = [
        {"day_range": "Day 1-4", "place": "Frankfurt"},  # Start in central Europe
        {"day_range": "Day 5-8", "place": "Naples"},     # Fly south to Naples
        {"day_range": "Day 9-11", "place": "Valencia"}, # Fly west to Valencia
        {"day_range": "Day 12-14", "place": "Oslo"},     # Fly north to Oslo
        {"day_range": "Day 15-16", "place": "Vilnius"}   # Fly east to Vilnius
    ]
    return {"itinerary": itinerary}

# Output the result
print(json.dumps(generate_itinerary()))