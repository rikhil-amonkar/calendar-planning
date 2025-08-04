import json
from collections import defaultdict

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Warsaw": (4, None),
        "Venice": (3, None),
        "Vilnius": (3, None),
        "Salzburg": (4, [(22, 25)]),
        "Amsterdam": (2, None),
        "Barcelona": (5, [(2, 6)]),
        "Paris": (2, [(1, 2)]),
        "Hamburg": (4, [(19, 22)]),
        "Florence": (5, None),
        "Tallinn": (2, [(11, 12)])
    }
    
    # Define the direct flights
    flights = [
        ("Paris", "Venice"), ("Barcelona", "Amsterdam"), ("Amsterdam", "Warsaw"),
        ("Amsterdam", "Vilnius"), ("Barcelona", "Warsaw"), ("Warsaw", "Venice"),
        ("Amsterdam", "Hamburg"), ("Barcelona", "Hamburg"), ("Barcelona", "Florence"),
        ("Barcelona", "Venice"), ("Paris", "Hamburg"), ("Paris", "Vilnius"),
        ("Paris", "Amsterdam"), ("Paris", "Florence"), ("Florence", "Amsterdam"),
        ("Vilnius", "Warsaw"), ("Barcelona", "Tallinn"), ("Paris", "Warsaw"),
        ("Tallinn", "Warsaw"), ("Tallinn", "Vilnius"), ("Amsterdam", "Tallinn"),
        ("Paris", "Tallinn"), ("Paris", "Barcelona"), ("Venice", "Hamburg"),
        ("Warsaw", "Hamburg"), ("Hamburg", "Salzburg"), ("Amsterdam", "Venice")
    ]
    
    # Create a graph for the flights
    graph = defaultdict(list)
    for a, b in flights:
        graph[a].append(b)
        graph[b].append(a)
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    visited = set()
    
    # Helper function to find the next city
    def find_next_city(current_city):
        for city in graph[current_city]:
            if city not in visited:
                return city
        return None
    
    # Start from Paris due to the workshop constraint
    current_city = "Paris"
    visited.add(current_city)
    
    while current_day <= 25:
        days_to_stay, events = constraints[current_city]
        
        # Check if there are any specific events that require staying longer
        if events:
            for start, end in events:
                if current_day >= start and current_day <= end:
                    days_to_stay = max(days_to_stay, end - current_day + 1)
        
        # Calculate the end day for the current city
        end_day = min(current_day + days_to_stay - 1, 25)
        
        # Add the current city to the itinerary
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": current_city})
        
        # Move to the next day
        current_day = end_day + 1
        
        # If we have reached the end of the trip, break
        if current_day > 25:
            break
        
        # Find the next city to visit
        next_city = find_next_city(current_city)
        if next_city:
            current_city = next_city
            visited.add(current_city)
        else:
            # If no next city is found, try to find a city with remaining days
            for city in constraints:
                if city not in visited:
                    current_city = city
                    visited.add(current_city)
                    break
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))