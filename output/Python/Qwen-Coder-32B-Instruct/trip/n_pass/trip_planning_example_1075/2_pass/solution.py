import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }
    
    # Define the flight connections
    flights = {
        "Reykjavik": ["Stuttgart", "Split", "Vienna"],
        "Stuttgart": ["Reykjavik", "Vienna", "Edinburgh", "Manchester", "Prague", "Lyon", "Split"],
        "Prague": ["Manchester", "Edinburgh", "Vienna", "Split", "Lyon", "Reykjavik"],
        "Edinburgh": ["Prague", "Stuttgart", "Vienna"],
        "Manchester": ["Prague", "Stuttgart", "Split"],
        "Vienna": ["Prague", "Edinburgh", "Stuttgart", "Lyon", "Reykjavik", "Manchester", "Split"],
        "Lyon": ["Vienna", "Stuttgart", "Split", "Prague"],
        "Split": ["Manchester", "Stuttgart", "Lyon", "Prague", "Vienna", "Reykjavik"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Add fixed events
    fixed_events = {
        "Edinburgh": (5, 8),
        "Split": (19, 23)
    }
    
    # Create a list of places to visit with their durations
    places_to_visit = [(city, duration) for city, duration in constraints.items()]
    
    # Sort places to visit by duration in descending order
    places_to_visit.sort(key=lambda x: x[1], reverse=True)
    
    # Function to check if a city can be visited on a given day
    def can_visit(city, day):
        for event_city, (start, end) in fixed_events.items():
            if event_city == city and not (day < start or day > end):
                return False
        return True
    
    # Function to find the next possible city to visit
    def find_next_city(current_city, current_day):
        for city, _ in places_to_visit:
            if city != current_city and can_visit(city, current_day) and current_city in flights and city in flights[current_city]:
                return city
        return None
    
    # Start from Reykjavik as it has a long stay and good connectivity
    current_city = "Reykjavik"
    
    while current_day <= 25:
        # Find the duration for the current city
        duration = constraints[current_city]
        
        # Check if the current city has a fixed event
        if current_city in fixed_events:
            start, end = fixed_events[current_city]
            if current_day >= start and current_day <= end:
                duration = min(duration, end - current_day + 1)
        
        # Ensure we do not exceed 25 days
        if current_day + duration > 25:
            duration = 25 - current_day
        
        # Add the current city to the itinerary
        itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": current_city})
        
        # Move to the next day
        current_day += duration
        
        # If we have reached or exceeded 25 days, break the loop
        if current_day >= 25:
            break
        
        # Find the next city to visit
        next_city = find_next_city(current_city, current_day)
        
        if next_city:
            # Add travel day
            itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": f"{current_city} to {next_city}"})
            current_day += 1
            current_city = next_city
        else:
            break
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))