import json

def calculate_itinerary():
    # Define the constraints
    total_days = 23
    stays = [
        ("Amsterdam", 1, 4),    # Day 1-4
        ("Brussels", 5, 9),     # Day 5-9
        ("Reykjavik", 10, 14),  # Day 10-14
        ("Berlin", 15, 19),     # Day 15-19
        ("Vienna", 20, 23)      # Day 20-23
    ]
    
    # Initialize the itinerary
    itinerary = []
    
    def add_to_itinerary(city, start_day, end_day):
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    
    # Add each city to the itinerary based on the defined stays
    for city, start_day, end_day in stays:
        add_to_itinerary(city, start_day, end_day)
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=2))