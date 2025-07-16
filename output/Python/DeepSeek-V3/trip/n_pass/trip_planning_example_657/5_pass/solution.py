import json

def generate_itinerary():
    # Improved itinerary with optimized geographical flow
    itinerary = [
        {"day_range": "Day 1-4", "place": "Vilnius"},     # Start in eastern Europe
        {"day_range": "Day 5-8", "place": "Frankfurt"},   # Travel west to central Europe
        {"day_range": "Day 9-11", "place": "Valencia"},   # Travel southwest to western Europe
        {"day_range": "Day 12-14", "place": "Naples"},    # Travel southeast to southern Europe
        {"day_range": "Day 15-16", "place": "Oslo"}       # Travel north to northern Europe
    ]
    return {"itinerary": itinerary}

# Output the result
print(json.dumps(generate_itinerary()))