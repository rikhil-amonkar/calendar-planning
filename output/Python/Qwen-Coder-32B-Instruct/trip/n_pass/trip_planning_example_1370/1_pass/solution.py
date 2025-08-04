import json
from collections import defaultdict

# Define the constraints
constraints = {
    "Santorini": {"days": 5, "preferred_range": (25, 29)},
    "Krakow": {"days": 5, "preferred_range": (18, 22)},
    "Paris": {"days": 5, "preferred_range": (11, 15)},
    "Vilnius": {"days": 3},
    "Munich": {"days": 5},
    "Geneva": {"days": 2},
    "Amsterdam": {"days": 4},
    "Budapest": {"days": 5},
    "Split": {"days": 4}
}

# Define the direct flight connections
connections = {
    "Paris": ["Krakow", "Amsterdam", "Split", "Geneva"],
    "Krakow": ["Paris", "Vilnius", "Split", "Amsterdam", "Munich"],
    "Amsterdam": ["Paris", "Munich", "Budapest", "Geneva", "Split"],
    "Vilnius": ["Krakow", "Munich", "Split", "Amsterdam", "Paris"],
    "Munich": ["Krakow", "Vilnius", "Split", "Amsterdam", "Geneva", "Budapest", "Paris"],
    "Geneva": ["Paris", "Amsterdam", "Munich", "Split", "Santorini", "Budapest"],
    "Budapest": ["Amsterdam", "Munich", "Geneva", "Paris"],
    "Split": ["Krakow", "Munich", "Geneva", "Amsterdam", "Vilnius"],
    "Santorini": ["Geneva", "Amsterdam"]
}

def find_itinerary(constraints, connections):
    itinerary = []
    day = 1
    remaining_days = 30
    
    # Create a sorted list of cities by preferred range start
    preferred_cities = sorted(
        [(city, info["preferred_range"][0]) for city, info in constraints.items() if "preferred_range" in info],
        key=lambda x: x[1]
    )
    
    # Add preferred cities first
    for city, _ in preferred_cities:
        info = constraints[city]
        preferred_start, preferred_end = info["preferred_range"]
        
        # Adjust the start day to fit within the preferred range
        if day < preferred_start:
            day = preferred_start
        
        # Calculate the end day
        end_day = min(day + info["days"] - 1, preferred_end)
        if end_day < day + info["days"] - 1:
            raise ValueError(f"Cannot fit {city} within its preferred range.")
        
        itinerary.append({"day_range": f"Day {day}-{end_day}", "place": city})
        day = end_day + 1
        remaining_days -= info["days"]
    
    # Add remaining cities
    for city, info in constraints.items():
        if "preferred_range" in info:
            continue
        
        if remaining_days < info["days"]:
            raise ValueError(f"Not enough days left to visit {city}.")
        
        # Find the next possible city to fly to
        last_city = itinerary[-1]["place"] if itinerary else None
        possible_flights = connections[last_city] if last_city else list(connections.keys())
        
        # Find the nearest city that can be reached
        next_city = None
        for c in possible_flights:
            if c in constraints and "preferred_range" not in constraints[c]:
                next_city = c
                break
        
        if not next_city:
            raise ValueError("Cannot find a valid itinerary.")
        
        end_day = day + info["days"] - 1
        itinerary.append({"day_range": f"Day {day}-{end_day}", "place": next_city})
        day = end_day + 1
        remaining_days -= info["days"]
    
    return itinerary

itinerary = find_itinerary(constraints, connections)
output = {"itinerary": itinerary}
print(json.dumps(output))