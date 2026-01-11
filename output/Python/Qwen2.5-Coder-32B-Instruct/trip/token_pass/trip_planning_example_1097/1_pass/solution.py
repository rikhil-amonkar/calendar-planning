import json

# Define the constraints
constraints = {
    "Reykjavik": 4,
    "Riga": 2,
    "Oslo": 3,
    "Lyon": 5,
    "Dubrovnik": 2,
    "Madrid": 2,
    "Warsaw": 4,
    "London": 3
}

# Define the event constraints
events = {
    "Riga": (4, 5),
    "Dubrovnik": (7, 8)
}

# Define the flight connections
flight_connections = {
    "Warsaw": ["Reykjavik", "Riga", "Oslo", "London", "Madrid"],
    "Oslo": ["Madrid", "Dubrovnik", "Oslo", "Lyon", "London", "Reykjavik", "Riga"],
    "Lyon": ["London", "Madrid", "Oslo"],
    "Madrid": ["London", "Lyon", "Oslo", "Warsaw", "Reykjavik"],
    "Dubrovnik": ["Oslo", "Madrid"],
    "Reykjavik": ["Warsaw", "Oslo", "Madrid", "London"],
    "Riga": ["Oslo", "Warsaw"],
    "London": ["Lyon", "Madrid", "Oslo", "Reykjavik", "Warsaw"]
}

# Function to check if a transition is valid
def is_valid_transition(current_city, next_city):
    return next_city in flight_connections[current_city]

# Function to build the itinerary
def build_itinerary(constraints, events, flight_connections):
    # Start with an empty itinerary
    itinerary = []
    current_day = 1
    
    # List of cities to visit, sorted by priority (fixed duration first)
    cities_to_visit = list(constraints.keys())
    
    # Sort cities by fixed duration and event constraints
    cities_to_visit.sort(key=lambda x: (-constraints[x], x in events))
    
    # Place the cities in the itinerary
    for city in cities_to_visit:
        duration = constraints[city]
        # Check if we can place this city in the current day range
        if city in events:
            event_start, event_end = events[city]
            if current_day <= event_start <= current_day + duration - 1:
                # Adjust the current day to start at the event day
                current_day = event_start
        # Add the city to the itinerary
        itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
        # Move to the next day after this city
        current_day += duration
    
    # Validate the itinerary
    if current_day != 19:
        raise ValueError("Itinerary does not cover exactly 18 days.")
    
    # Check event constraints
    for city, (event_start, event_end) in events.items():
        found = False
        for entry in itinerary:
            day_start, day_end = map(int, entry["day_range"].split("-")[0].split()[1]), map(int, entry["day_range"].split("-")[1])
            if city == entry["place"] and event_start in range(day_start, day_end + 1):
                found = True
                break
        if not found:
            raise ValueError(f"Event in {city} not scheduled correctly.")
    
    # Check flight connections
    for i in range(len(itinerary) - 1):
        current_city = itinerary[i]["place"]
        next_city = itinerary[i + 1]["place"]
        if not is_valid_transition(current_city, next_city):
            raise ValueError(f"No direct flight from {current_city} to {next_city}.")
    
    return itinerary

# Build the itinerary
itinerary = build_itinerary(constraints, events, flight_connections)

# Output the itinerary as a JSON object
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))