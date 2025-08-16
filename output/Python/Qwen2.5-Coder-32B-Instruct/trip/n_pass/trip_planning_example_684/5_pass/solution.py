import json

def calculate_itinerary(stays, total_days):
    # Validate the input stays
    if not stays:
        raise ValueError("No stays provided.")
    
    # Sort stays by start day to ensure chronological order
    stays.sort(key=lambda x: x[1])
    
    # Initialize the itinerary
    itinerary = []
    
    def add_to_itinerary(city, start_day, end_day):
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    
    # Check for overlapping days and add each city to the itinerary
    last_end_day = 0
    for city, start_day, end_day in stays:
        if start_day <= last_end_day:
            raise ValueError(f"Overlapping days detected between {city} and previous stay.")
        if end_day > total_days:
            raise ValueError(f"Stay for {city} exceeds total days allowed.")
        add_to_itinerary(city, start_day, end_day)
        last_end_day = end_day
    
    return {"itinerary": itinerary}

# Define the constraints
total_days = 23
stays = [
    ("Amsterdam", 1, 4),    # Day 1-4
    ("Brussels", 5, 9),     # Day 5-9
    ("Reykjavik", 10, 14),  # Day 10-14
    ("Berlin", 15, 19),     # Day 15-19
    ("Vienna", 20, 23)      # Day 20-23
]

# Calculate and print the itinerary
try:
    itinerary = calculate_itinerary(stays, total_days)
    print(json.dumps(itinerary, indent=2))
except ValueError as e:
    print(f"Error: {e}")