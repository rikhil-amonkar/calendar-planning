import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Helsinki": {"days": 2, "workshop": (1, 2)},
        "Warsaw": {"days": 3, "relatives": (9, 11)},
        "Madrid": {"days": 4},
        "Split": {"days": 4},
        "Reykjavik": {"days": 2, "friend": (8, 9)},
        "Budapest": {"days": 4}
    }
    
    # Define the direct flight connections
    flights = {
        "Helsinki": ["Reykjavik", "Split", "Madrid", "Budapest", "Warsaw"],
        "Reykjavik": ["Helsinki", "Warsaw", "Madrid", "Budapest"],
        "Split": ["Helsinki", "Warsaw", "Madrid"],
        "Madrid": ["Helsinki", "Split", "Warsaw", "Budapest", "Reykjavik"],
        "Warsaw": ["Helsinki", "Reykjavik", "Madrid", "Split", "Budapest"],
        "Budapest": ["Helsinki", "Reykjavik", "Madrid", "Warsaw"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None
    
    def add_to_itinerary(city, start_day, end_day):
        nonlocal itinerary
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    
    # Place Helsinki first due to workshop constraint
    add_to_itinerary("Helsinki", 1, 2)
    current_day = 3
    current_city = "Helsinki"
    
    # Move to Reykjavik to meet a friend between day 8 and day 9
    while current_day < 8:
        next_city = "Reykjavik" if "Reykjavik" in flights[current_city] else flights[current_city][0]
        add_to_itinerary(next_city, current_day, current_day + 1)
        current_day += 1
        current_city = next_city
    
    # Stay in Reykjavik for 2 days, meeting friend on day 8
    add_to_itinerary("Reykjavik", 8, 9)
    current_day = 10
    current_city = "Reykjavik"
    
    # Move to Warsaw to visit relatives between day 9 and day 11
    while current_day < 9:
        next_city = "Warsaw" if "Warsaw" in flights[current_city] else flights[current_city][0]
        add_to_itinerary(next_city, current_day, current_day + 1)
        current_day += 1
        current_city = next_city
    
    # Stay in Warsaw for 3 days, visiting relatives on day 9-11
    add_to_itinerary("Warsaw", 9, 11)
    current_day = 12
    current_city = "Warsaw"
    
    # Remaining days to be filled with Madrid, Split, and Budapest
    remaining_cities = ["Madrid", "Split", "Budapest"]
    remaining_days = 14 - current_day + 1
    
    # Assign days to remaining cities
    for city in remaining_cities:
        days_in_city = constraints[city]["days"]
        add_to_itinerary(city, current_day, current_day + days_in_city - 1)
        current_day += days_in_city
        current_city = city
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))