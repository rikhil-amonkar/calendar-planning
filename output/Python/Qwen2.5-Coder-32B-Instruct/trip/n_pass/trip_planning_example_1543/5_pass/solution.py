import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Prague": (3, [1, 3]),
        "Warsaw": (4, [20, 23]),
        "Dublin": (3, []),
        "Athens": (3, []),
        "Vilnius": (4, []),
        "Porto": (5, [16, 20]),
        "London": (3, [10, 12]),  # Corrected mandatory days
        "Seville": (2, []),
        "Lisbon": (5, [21, 25]),  # Corrected mandatory days
        "Dubrovnik": (3, [])
    }
    
    # Define the direct flight connections
    connections = {
        "Warsaw": ["Vilnius", "Prague", "London", "Lisbon", "Athens", "Porto"],
        "Prague": ["Athens", "Lisbon", "London", "Warsaw", "Dublin"],
        "Dublin": ["Prague", "Athens", "Seville", "Porto", "Lisbon"],
        "Athens": ["Prague", "Dublin", "Vilnius", "Lisbon", "Dubrovnik", "Warsaw"],
        "Vilnius": ["Athens", "Warsaw", "Prague"],
        "Porto": ["Lisbon", "Dublin", "Seville", "Warsaw", "Athens"],
        "London": ["Prague", "Lisbon", "Warsaw"],
        "Seville": ["Dublin", "Porto", "Lisbon"],
        "Lisbon": ["London", "Seville", "Athens", "Dublin", "Porto", "Warsaw"],
        "Dubrovnik": ["Athens", "Lisbon", "Dublin"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = "Prague"  # Start in Prague
    
    # List of visited cities
    visited_cities = set()
    
    # Build the itinerary
    while current_day <= 26:
        # Get the duration and mandatory days for the current city
        duration, mandatory_days = constraints[current_city]
        
        # Determine the start and end days for the current city
        if mandatory_days:
            start_day = max(current_day, mandatory_days[0])
            end_day = min(start_day + duration - 1, mandatory_days[1], 26)
        else:
            start_day = current_day
            end_day = min(start_day + duration - 1, 26)
        
        # Add the current city to the itinerary
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
        
        # Update the current day and mark the city as visited
        current_day = end_day + 1
        visited_cities.add(current_city)
        
        # Find the next city to visit
        next_city = None
        for city in connections[current_city]:
            if city not in visited_cities:
                next_city = city
                break
        
        if next_city is None:
            # If no unvisited connected city is found, try any unvisited city
            for city in constraints.keys():
                if city not in visited_cities:
                    next_city = city
                    break
        
        current_city = next_city
    
    # Ensure the itinerary covers exactly 26 days
    if current_day > 26:
        # Remove the last entry if it exceeds 26 days
        itinerary.pop()
        current_day -= constraints[itinerary[-1]["place"]][0]
    
    if current_day < 26:
        # Fill the remaining days with the last visited city
        last_city = itinerary[-1]["place"]
        last_duration = constraints[last_city][0]
        start_day = current_day
        end_day = min(start_day + last_duration - 1, 26)
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": last_city})
    
    # Adjust the itinerary to ensure exact 26 days
    adjusted_itinerary = []
    current_day = 1
    for entry in itinerary:
        start_day, end_day = map(int, entry["day_range"].split('-')[1].split(' '))
        if start_day > current_day:
            # Fill the gap with the previous city
            previous_city = adjusted_itinerary[-1]["place"]
            adjusted_itinerary.append({"day_range": f"Day {current_day}-{start_day-1}", "place": previous_city})
            current_day = start_day
        adjusted_itinerary.append(entry)
        current_day = end_day + 1
    
    if current_day < 26:
        # Fill the remaining days with the last visited city
        last_city = adjusted_itinerary[-1]["place"]
        adjusted_itinerary.append({"day_range": f"Day {current_day}-26", "place": last_city})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": adjusted_itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))