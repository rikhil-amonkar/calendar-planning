import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2,
        "show_in_helsinki": (2, 5),  # Show from Day 2 to Day 5
        "workshop_in_prague": (1, 2)  # Workshop from Day 1 to Day 2
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start with Prague due to the workshop constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Prague'] - 1}", "place": "Prague"})
    current_day += constraints["Prague"]
    
    # Move to Helsinki for the show
    itinerary.append({"day_range": f"Day {current_day}-{constraints['show_in_helsinki'][1]}", "place": "Helsinki"})
    current_day = constraints["show_in_helsinki"][1] + 1
    
    # Stay in Helsinki until the required days are completed
    if current_day < constraints["Helsinki"] + 1:
        itinerary.append({"day_range": f"Day {current_day}-{constraints['Helsinki']}", "place": "Helsinki"})
        current_day = constraints["Helsinki"] + 1
    
    # Move to Frankfurt
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Frankfurt'] - 1}", "place": "Frankfurt"})
    current_day += constraints["Frankfurt"]
    
    # Move to Naples
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Naples'] - 1}", "place": "Naples"})
    current_day += constraints["Naples"]
    
    # Move to Lyon
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Lyon'] - 1}", "place": "Lyon"})
    current_day += constraints["Lyon"]
    
    # Ensure the total number of days is exactly 12
    if current_day != 13:
        raise ValueError("Itinerary does not cover exactly 12 days")
    
    # Output the itinerary in JSON format
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())