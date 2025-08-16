import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }
    
    # Define the flight connections
    flights = [
        ("Helsinki", "London"), ("Split", "Madrid"), ("Helsinki", "Madrid"),
        ("London", "Madrid"), ("Brussels", "London"), ("Bucharest", "London"),
        ("Brussels", "Bucharest"), ("Bucharest", "Madrid"), ("Split", "Helsinki"),
        ("Mykonos", "Madrid"), ("Stuttgart", "London"), ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"), ("Split", "London"), ("Stuttgart", "Split"),
        ("London", "Mykonos")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Add fixed constraints first
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Madrid'] - 1}", "place": "Madrid"})
    current_day += constraints['Madrid']
    
    # Add Brussels
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Brussels'] - 1}", "place": "Brussels"})
    current_day += constraints['Brussels']
    
    # Add Bucharest
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Bucharest'] - 1}", "place": "Bucharest"})
    current_day += constraints['Bucharest']
    
    # Add Stuttgart
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Stuttgart'] - 1}", "place": "Stuttgart"})
    current_day += constraints['Stuttgart']
    
    # Add Mykonos
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Mykonos'] - 1}", "place": "Mykonos"})
    current_day += constraints['Mykonos']
    
    # Add Split
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Split'] - 1}", "place": "Split"})
    current_day += constraints['Split']
    
    # Add Helsinki
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Helsinki'] - 1}", "place": "Helsinki"})
    current_day += constraints['Helsinki']
    
    # Add remaining days to London
    itinerary.append({"day_range": f"Day {current_day}-Day 21", "place": "London"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
print(json.dumps({"itinerary": itinerary}))