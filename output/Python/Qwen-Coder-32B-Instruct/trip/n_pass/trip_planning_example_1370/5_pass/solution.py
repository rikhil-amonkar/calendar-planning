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
    
    # Collect cities without preferred ranges
    non_preferred_cities = [city for city, info in constraints.items() if "preferred_range" not in info]
    
    # Try to fit non-preferred cities into the remaining days
    while non_preferred_cities and remaining_days > 0:
        placed = False
        for city in non_preferred_cities[:]:  # Iterate over a copy of the list
            info = constraints[city]
            if remaining_days >= info["days"]:
                # Find the next possible city to fly to
                last_city = itinerary[-1]["place"] if itinerary else None
                possible_flights = connections[last_city] if last_city else list(connections.keys())
                
                # Check if the city can be reached from the last city in the itinerary
                if last_city is None or city in possible_flights:
                    end_day = day + info["days"] - 1
                    if end_day <= 30:
                        itinerary.append({"day_range": f"Day {day}-{end_day}", "place": city})
                        day = end_day + 1
                        remaining_days -= info["days"]
                        non_preferred_cities.remove(city)
                        placed = True
                        break
        if not placed:
            # If no city can be placed, try to backtrack and find another valid placement
            for i in range(len(itinerary) - 1, -1, -1):
                last_city_info = itinerary[i]
                last_city = last_city_info["place"]
                last_city_days = constraints[last_city]["days"]
                new_day = last_city_info["day_range"].split('-')[0].split(' ')[1]
                new_day = int(new_day) + 1
                
                if new_day + info["days"] - 1 <= 30:
                    day = new_day
                    remaining_days += last_city_days
                    del itinerary[i:]
                    break
            else:
                raise ValueError("Cannot find a valid itinerary for all cities.")
    
    return itinerary

try:
    itinerary = find_itinerary(constraints, connections)
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
except ValueError as e:
    print(f"Error: {e}")