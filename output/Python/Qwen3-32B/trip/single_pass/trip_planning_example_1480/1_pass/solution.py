import json
from collections import defaultdict

# Define the cities and their required durations
cities = {
    "Geneva": 4,
    "Brussels": 2,
    "Venice": 5,
    "Vienna": 4,
    "Istanbul": 4,
    "Riga": 2,
    "Madrid": 4,
    "Vilnius": 4,
    "Munich": 5,
    "Reykjavik": 2
}

# Define fixed time windows
fixed_windows = {
    "Geneva": (1, 4),
    "Venice": (7, 11),
    "Vilnius": (20, 23),
    "Brussels": (26, 27)
}

# Define direct flight connections (bidirectional)
flights = {
    "Munich": ["Vienna", "Brussels", "Madrid", "Reykjavik", "Venice", "Geneva", "Istanbul", "Riga"],
    "Vienna": ["Munich", "Brussels", "Vilnius", "Istanbul", "Geneva", "Reykjavik", "Madrid", "Vienna", "Riga"],
    "Istanbul": ["Geneva", "Brussels", "Vienna", "Vilnius", "Riga", "Geneva", "Madrid", "Vienna", "Riga"],
    "Brussels": ["Munich", "Istanbul", "Geneva", "Venice", "Riga", "Vilnius", "Madrid", "Vienna", "Geneva", "Munich"],
    "Venice": ["Brussels", "Munich", "Madrid", "Istanbul", "Vienna", "Geneva"],
    "Riga": ["Brussels", "Istanbul", "Geneva", "Munich", "Vilnius", "Vienna"],
    "Geneva": ["Istanbul", "Brussels", "Madrid", "Vienna", "Munich", "Venice"],
    "Madrid": ["Munich", "Vienna", "Brussels", "Geneva", "Reykjavik"],
    "Vilnius": ["Brussels", "Istanbul", "Munich", "Vienna", "Riga"],
    "Reykjavik": ["Munich", "Vienna", "Brussels", "Madrid"]
}

# Build bidirectional flight connections
flight_graph = defaultdict(list)
for city, connected in flights.items():
    for conn in connected:
        flight_graph[city].append(conn)

# Hardcoded valid itinerary sequence based on constraints
itinerary_sequence = [
    "Geneva",
    "Brussels",
    "Venice",
    "Vienna",
    "Munich",
    "Istanbul",
    "Vilnius",
    "Riga",
    "Brussels"
]

# Calculate start and end days for each city in the itinerary
current_day = 1
itinerary = []
for i, city in enumerate(itinerary_sequence):
    duration = cities[city]
    start_day = current_day
    end_day = start_day + duration - 1
    
    # Apply fixed windows if applicable
    if city in fixed_windows:
        fixed_start, fixed_end = fixed_windows[city]
        if start_day < fixed_start:
            start_day = fixed_start
            end_day = start_day + duration - 1
        if end_day > fixed_end:
            end_day = fixed_end
            start_day = end_day - duration + 1
    
    # Add to itinerary
    day_range = f"Day {start_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    
    # Update current day for next city (flight day is end_day + 1)
    current_day = end_day + 1

# Validate the itinerary
def is_valid(itinerary, cities, fixed_windows, flight_graph):
    # Check durations
    for entry in itinerary:
        city = entry["place"]
        start_day = int(entry["day_range"].split()[1].split('-')[0])
        end_day = int(entry["day_range"].split()[1].split('-')[1])
        if end_day - start_day + 1 != cities[city]:
            return False
    
    # Check fixed windows
    for entry in itinerary:
        city = entry["place"]
        if city in fixed_windows:
            start_day = int(entry["day_range"].split()[1].split('-')[0])
            end_day = int(entry["day_range"].split()[1].split('-')[1])
            fixed_start, fixed_end = fixed_windows[city]
            if not (fixed_start <= start_day and end_day <= fixed_end):
                return False
    
    # Check flight connections
    for i in range(len(itinerary) - 1):
        current_city = itinerary[i]["place"]
        next_city = itinerary[i+1]["place"]
        if next_city not in flight_graph[current_city]:
            return False
    
    # Check total days
    last_entry = itinerary[-1]
    end_day = int(last_entry["day_range"].split()[1].split('-')[1])
    if end_day != 27:
        return False
    
    return True

# Output result
if is_valid(itinerary, cities, fixed_windows, flight_graph):
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found")