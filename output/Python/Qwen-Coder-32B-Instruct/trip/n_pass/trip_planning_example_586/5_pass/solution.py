import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2,
        "show_in_helsinki": (3, 6),  # Show from Day 3 to Day 6
        "workshop_in_prague": (1, 2)  # Workshop from Day 1 to Day 2
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start with Prague due to the workshop constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Prague'] - 1}", "place": "Prague"})
    current_day += constraints["Prague"]
    
    # Move to Helsinki for the show
    # The show is from Day 3 to Day 6, so we need to make sure we start at Day 3
    if current_day > constraints['show_in_helsinki'][0]:
        raise ValueError("Cannot start show in Helsinki before the workshop ends")
    
    # Adjust current_day to start the show in Helsinki
    current_day = constraints['show_in_helsinki'][0]
    itinerary.append({"day_range": f"Day {current_day}-{constraints['show_in_helsinki'][1]}", "place": "Helsinki"})
    current_day = constraints['show_in_helsinki'][1] + 1
    
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
        raise ValueError(f"Itinerary does not cover exactly 12 days, it covers {current_day - 1} days")
    
    # Output the itinerary in JSON format
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())