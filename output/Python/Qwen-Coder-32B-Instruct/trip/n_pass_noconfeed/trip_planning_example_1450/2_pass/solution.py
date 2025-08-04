import json
from collections import deque

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5
    }
    
    # Define the fixed events
    fixed_events = {
        "Istanbul": (25, 29),
        "Krakow": (5, 9)
    }
    
    # Define the direct flights
    direct_flights = [
        ("Oslo", "Stockholm"), ("Krakow", "Frankfurt"), ("Krakow", "Istanbul"),
        ("Munich", "Stockholm"), ("Hamburg", "Stockholm"), ("Krakow", "Vilnius"),
        ("Oslo", "Istanbul"), ("Istanbul", "Stockholm"), ("Oslo", "Krakow"),
        ("Vilnius", "Istanbul"), ("Oslo", "Vilnius"), ("Frankfurt", "Istanbul"),
        ("Oslo", "Frankfurt"), ("Munich", "Hamburg"), ("Munich", "Istanbul"),
        ("Oslo", "Munich"), ("Frankfurt", "Florence"), ("Oslo", "Hamburg"),
        ("Vilnius", "Frankfurt"), ("Florence", "Munich"), ("Krakow", "Munich"),
        ("Hamburg", "Istanbul"), ("Frankfurt", "Stockholm"), ("Stockholm", "Santorini"),
        ("Frankfurt", "Munich"), ("Santorini", "Oslo"), ("Krakow", "Stockholm"),
        ("Vilnius", "Munich"), ("Frankfurt", "Hamburg")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Add fixed events first
    for city, (start, end) in fixed_events.items():
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        current_day = end + 1
    
    # Sort constraints by priority (fixed events already added)
    remaining_cities = sorted(constraints.items(), key=lambda x: (x[0] in fixed_events, x[1]), reverse=True)
    
    # Function to check if a flight exists between two cities
    def can_fly(city1, city2):
        return (city1, city2) in direct_flights or (city2, city1) in direct_flights
    
    # Function to find a path from start_city to end_city using BFS
    def find_path(start_city, end_city):
        queue = deque([(start_city, [start_city])])
        visited = set([start_city])
        
        while queue:
            current_city, path = queue.popleft()
            if current_city == end_city:
                return path
            for neighbor in constraints:
                if can_fly(current_city, neighbor) and neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        
        return None
    
    # Add remaining cities to the itinerary
    for city, days in remaining_cities:
        if any(city in event for event in fixed_events):
            continue
        
        # Find a valid starting day for this city
        while True:
            valid_start = True
            for event in fixed_events.values():
                if current_day >= event[0] and current_day <= event[1]:
                    valid_start = False
                    current_day = event[1] + 1
                    break
            
            if valid_start:
                break
        
        # Check if we can fly to this city from the last city in the itinerary
        if itinerary:
            last_city = itinerary[-1]["place"]
            if not can_fly(last_city, city):
                # Find a connecting path
                path = find_path(last_city, city)
                if not path:
                    raise Exception(f"No valid flight path found to {city} from {last_city}")
                # Add intermediate cities to the itinerary
                for connecting_city in path[1:-1]:
                    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": connecting_city})
                    current_day += 1
        
        # Add the city to the itinerary
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))