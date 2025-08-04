import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Helsinki": {"days": 2, "workshop": (1, 2)},
        "Warsaw": {"days": 3, "relatives": (9, 11)},
        "Madrid": {"days": 3},
        "Split": {"days": 2},
        "Reykjavik": {"days": 2, "friend": (8, 9)},
        "Budapest": {"days": 2}
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Place Helsinki first due to workshop constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Helsinki']['days'] - 1}", "place": "Helsinki"})
    current_day += constraints['Helsinki']['days']
    
    # Place Budapest next to fit within the remaining days and constraints
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Budapest']['days'] - 1}", "place": "Budapest"})
    current_day += constraints['Budapest']['days']
    
    # Place Reykjavik next due to friend meeting constraint
    # Adjust current_day to start at day 8
    current_day = 8
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Reykjavik']['days'] - 1}", "place": "Reykjavik"})
    current_day += constraints['Reykjavik']['days']
    
    # Place Warsaw next due to relatives visit constraint
    # Adjust current_day to start at day 9
    current_day = 9
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Warsaw']['days'] - 1}", "place": "Warsaw"})
    current_day += constraints['Warsaw']['days']
    
    # Place Madrid next
    # Adjust current_day to start after Warsaw's stay
    current_day = 12
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Madrid']['days'] - 1}", "place": "Madrid"})
    current_day += constraints['Madrid']['days']
    
    # Place Split last
    # Adjust current_day to start after Madrid's stay
    current_day = 15
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Split']['days'] - 1}", "place": "Split"})
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=4))