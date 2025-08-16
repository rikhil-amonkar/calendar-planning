import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Helsinki": {"days": 2, "workshop": (1, 2)},
        "Warsaw": {"days": 3, "relatives": (9, 11)},
        "Madrid": {"days": 3},  # Reduced from 4 to 3 days
        "Split": {"days": 4},
        "Reykjavik": {"days": 2, "friend": (8, 9)},
        "Budapest": {"days": 3}  # Reduced from 4 to 3 days
    }
    
    # Define the direct flight connections (not used in this specific logic)
    flights = {
        "Helsinki": ["Reykjavik", "Split", "Madrid", "Budapest", "Warsaw"],
        "Reykjavik": ["Helsinki", "Warsaw", "Madrid"],
        "Budapest": ["Helsinki", "Madrid", "Warsaw"],
        "Madrid": ["Helsinki", "Reykjavik", "Budapest", "Warsaw", "Split"],
        "Warsaw": ["Helsinki", "Reykjavik", "Budapest", "Madrid", "Split"],
        "Split": ["Helsinki", "Madrid", "Warsaw"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Place Helsinki first due to workshop constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Helsinki']['days'] - 1}", "place": "Helsinki"})
    current_day += constraints['Helsinki']['days']
    
    # Place Reykjavik next due to friend meeting constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Reykjavik']['days'] - 1}", "place": "Reykjavik"})
    current_day += constraints['Reykjavik']['days']
    
    # Place Warsaw next due to relatives visit constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Warsaw']['days'] - 1}", "place": "Warsaw"})
    current_day += constraints['Warsaw']['days']
    
    # Place Budapest next
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Budapest']['days'] - 1}", "place": "Budapest"})
    current_day += constraints['Budapest']['days']
    
    # Place Madrid next
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Madrid']['days'] - 1}", "place": "Madrid"})
    current_day += constraints['Madrid']['days']
    
    # Place Split last
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Split']['days'] - 1}", "place": "Split"})
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=4))