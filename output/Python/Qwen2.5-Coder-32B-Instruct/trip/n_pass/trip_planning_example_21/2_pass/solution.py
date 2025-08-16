import json

def calculate_itinerary():
    # Input constraints
    total_days = 10
    venice_days = 6
    mykonos_days = 2
    vienna_days = 4
    venice_workshop_start = 5
    venice_workshop_end = 10
    direct_flights = {
        ("Mykonos", "Vienna"),
        ("Vienna", "Venice")
    }

    # Initialize itinerary
    itinerary = []

    # Determine the days for each city
    # Start with Vienna since it's the only starting point
    itinerary.append({"day_range": f"Day 1-{vienna_days}", "place": "Vienna"})
    
    # Next, go to Mykonos
    # Overlapping day is day 4
    start_day_mykonos = vienna_days - 1  # Day 4
    end_day_mykonos = start_day_mykonos + mykonos_days  # Day 5
    itinerary.append({"day_range": f"Day {start_day_mykonos}-{end_day_mykonos}", "place": "Mykonos"})
    
    # Finally, go to Venice
    # Overlapping day is day 5
    start_day_venice = end_day_mykonos - 1  # Day 5
    end_day_venice = start_day_venice + venice_days  # Day 10
    itinerary.append({"day_range": f"Day {start_day_venice}-{end_day_venice}", "place": "Venice"})

    # Validate the itinerary
    assert end_day_venice == total_days, "Itinerary does not match the total days constraint"
    assert venice_workshop_start <= end_day_venice <= venice_workshop_end, "Venice workshop constraint not met"

    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))