import json

def calculate_itinerary():
    # Define the constraints
    total_days = 21
    manchester_days = 3
    istanbul_days = 7
    venice_days = 7
    krakow_days = 6
    lyon_days = 2
    
    # Define the direct flight connections
    flights = {
        'Manchester': ['Venice', 'Istanbul', 'Krakow'],
        'Venice': ['Manchester', 'Istanbul', 'Lyon'],
        'Istanbul': ['Manchester', 'Venice', 'Krakow', 'Lyon'],
        'Krakow': ['Manchester', 'Istanbul'],
        'Lyon': ['Venice', 'Istanbul']
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Place constraints
    manchester_start = 1
    manchester_end = manchester_start + manchester_days - 1
    venice_start = 3
    venice_end = venice_start + venice_days - 1
    
    # Add Manchester to the itinerary
    itinerary.append({"day_range": f"Day {manchester_start}-{manchester_end}", "place": "Manchester"})
    current_day = manchester_end + 1
    
    # Add Venice to the itinerary
    itinerary.append({"day_range": f"Day {venice_start}-{venice_end}", "place": "Venice"})
    current_day = venice_end + 1
    
    # Add Istanbul to the itinerary
    istanbul_start = current_day
    istanbul_end = istanbul_start + istanbul_days - 1
    itinerary.append({"day_range": f"Day {istanbul_start}-{istanbul_end}", "place": "Istanbul"})
    current_day = istanbul_end + 1
    
    # Add Krakow to the itinerary
    krakow_start = current_day
    krakow_end = krakow_start + krakow_days - 1
    itinerary.append({"day_range": f"Day {krakow_start}-{krakow_end}", "place": "Krakow"})
    current_day = krakow_end + 1
    
    # Add Lyon to the itinerary
    lyon_start = current_day
    lyon_end = lyon_start + lyon_days - 1
    itinerary.append({"day_range": f"Day {lyon_start}-{lyon_end}", "place": "Lyon"})
    current_day = lyon_end + 1
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())