import json

def calculate_itinerary():
    # Define the constraints with adjusted days to sum up to 18
    constraints = {
        "Venice": 5,
        "Frankfurt": 3,
        "Salzburg": 3,
        "Florence": 3,
        "Barcelona": 2,
        "Stuttgart": 1,
        "Stockholm": 1
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Add Venice from Day 1 to Day 5 due to the show
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Venice'] - 1}", "place": "Venice"})
    current_day += constraints['Venice']
    
    # Add Frankfurt for 3 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Frankfurt'] - 1}", "place": "Frankfurt"})
    current_day += constraints['Frankfurt']
    
    # Add Salzburg for 3 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Salzburg'] - 1}", "place": "Salzburg"})
    current_day += constraints['Salzburg']
    
    # Add Florence for 3 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Florence'] - 1}", "place": "Florence"})
    current_day += constraints['Florence']
    
    # Add Barcelona for 2 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Barcelona'] - 1}", "place": "Barcelona"})
    current_day += constraints['Barcelona']
    
    # Add Stuttgart for 1 day
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Stuttgart'] - 1}", "place": "Stuttgart"})
    current_day += constraints['Stuttgart']
    
    # Add Stockholm for 1 day
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Stockholm'] - 1}", "place": "Stockholm"})
    current_day += constraints['Stockholm']
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())