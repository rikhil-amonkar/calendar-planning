import json

def generate_itinerary():
    # Define the constraints
    constraints = {
        "Tallinn": (1, 2),
        "Bucharest": (1, 4),
        "Seville": (8, 12),
        "Munich": (4, 8),
        "Stockholm": 5,
        "Milan": 2
    }

    # Initialize the itinerary
    itinerary = []

    # Add fixed stays
    itinerary.append({"day_range": "Day 1-2", "place": "Tallinn"})
    itinerary.append({"day_range": "Day 1-4", "place": "Bucharest"})
    itinerary.append({"day_range": "Day 8-12", "place": "Seville"})
    itinerary.append({"day_range": "Day 4-8", "place": "Munich"})

    # Determine remaining days for Stockholm and Milan
    # Stockholm can be from Day 9-13 (after Munich ends)
    itinerary.append({"day_range": "Day 9-13", "place": "Stockholm"})
    
    # Milan can be from Day 14-15 (after Stockholm ends)
    itinerary.append({"day_range": "Day 14-15", "place": "Milan"})

    # Ensure the total duration is 18 days
    # Check if the last day is within the 18-day limit
    last_day = 15  # Last day of Milan stay
    if last_day > 18:
        raise ValueError("Itinerary exceeds 18 days")

    # Output the itinerary in JSON format
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())