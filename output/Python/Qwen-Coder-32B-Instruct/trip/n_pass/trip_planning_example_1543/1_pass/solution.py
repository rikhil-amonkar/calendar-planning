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
        "London": (3, [3, 5]),
        "Seville": (2, []),
        "Lisbon": (5, [5, 9]),
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
    current_city = None
    
    # Function to find the next city to visit
    def find_next_city(current_city, visited_cities):
        for city, details in constraints.items():
            if city not in visited_cities:
                if current_city is None or city in connections[current_city]:
                    return city
        return None
    
    # List of visited cities
    visited_cities = set()
    
    # Build the itinerary
    while current_day <= 26:
        if current_city is None:
            current_city = "Prague"  # Start in Prague
        
        # Get the duration and mandatory days for the current city
        duration, mandatory_days = constraints[current_city]
        
        # Determine the start and end days for the current city
        if mandatory_days:
            start_day = max(current_day, mandatory_days[0])
            end_day = min(start_day + duration - 1, mandatory_days[1])
        else:
            start_day = current_day
            end_day = start_day + duration - 1
        
        # Adjust the end day if it exceeds the total trip duration
        if end_day > 26:
            end_day = 26
        
        # Add the current city to the itinerary
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
        
        # Update the current day and mark the city as visited
        current_day = end_day + 1
        visited_cities.add(current_city)
        
        # Find the next city to visit
        current_city = find_next_city(current_city, visited_cities)
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))