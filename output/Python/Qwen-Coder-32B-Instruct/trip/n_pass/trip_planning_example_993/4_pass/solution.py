import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }
    
    # Define the events
    events = {
        "Amsterdam": [(2, 3)],
        "Vilnius": [(7, 11)],
        "Stockholm": [(13, 15)]
    }
    
    # Define the flight connections
    flights = [
        ("London", "Amsterdam"),
        ("Vilnius", "Frankfurt"),
        ("Riga", "Vilnius"),
        ("Riga", "Stockholm"),
        ("London", "Bucharest"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Stockholm"),
        ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"),
        ("Amsterdam", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"),
        ("London", "Frankfurt"),
        ("London", "Stockholm"),
        ("Amsterdam", "Vilnius")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    visited_cities = set()
    
    # Helper function to check if a city can be visited on a given day
    def can_visit(city, day):
        if city not in constraints:
            return False
        for event_day in events.get(city, []):
            if event_day[0] <= day <= event_day[1]:
                return True
        return False
    
    # Helper function to find the next possible city to visit
    def find_next_city(current_city, current_day):
        for city in constraints:
            if city not in visited_cities and ((city, current_city) in flights or (current_city, city) in flights):
                if can_visit(city, current_day):
                    return city
        return None
    
    # Start from London as it has multiple connections
    current_city = "London"
    
    while current_day <= 15:
        # Find the duration for the current city
        duration = constraints[current_city]
        
        # Check if we need to adjust the duration for events
        for event_day in events.get(current_city, []):
            if event_day[0] <= current_day + duration - 1 <= event_day[1]:
                duration = max(duration, event_day[1] - current_day + 1)
        
        # Ensure the duration does not exceed the remaining days
        if current_day + duration > 15:
            duration = 15 - current_day + 1
        
        # Add the current city to the itinerary
        itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": current_city})
        
        # Mark the current city as visited
        visited_cities.add(current_city)
        
        # Move to the next day
        current_day += duration
        
        # Find the next city to visit
        next_city = find_next_city(current_city, current_day)
        if next_city and current_day <= 15:
            current_city = next_city
        else:
            # If no next city is found or we have reached the end, stay in the current city
            current_city = current_city
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))