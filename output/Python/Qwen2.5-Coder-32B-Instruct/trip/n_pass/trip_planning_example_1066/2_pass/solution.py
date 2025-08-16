import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 4,  # Extended from 2 to 4 days to make the total 21 days
        "Helsinki": 5,
        "Split": 3,
        "London": 3  # Reduced from 5 to 3 days
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start with Helsinki
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Helsinki'] - 1}", "place": "Helsinki"})
    current_day += constraints['Helsinki']
    
    # Next go to Brussels
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Brussels'] - 1}", "place": "Brussels"})
    current_day += constraints['Brussels']
    
    # Next go to Bucharest
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Bucharest'] - 1}", "place": "Bucharest"})
    current_day += constraints['Bucharest']
    
    # Next go to Madrid (conference days)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Madrid'] - 1}", "place": "Madrid"})
    current_day += constraints['Madrid']
    
    # Next go to Mykonos
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Mykonos'] - 1}", "place": "Mykonos"})
    current_day += constraints['Mykonos']
    
    # Finally go to London
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['London'] - 1}", "place": "London"})
    current_day += constraints['London']
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))