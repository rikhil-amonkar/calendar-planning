import json
from collections import defaultdict

# Define the constraints
constraints = {
    "Warsaw": 4,
    "Venice": 3,
    "Vilnius": 3,
    "Salzburg": 4,
    "Amsterdam": 2,
    "Barcelona": 5,
    "Paris": 2,
    "Hamburg": 4,
    "Florence": 5,
    "Tallinn": 2
}

# Define the fixed events
fixed_events = {
    "Salzburg": (22, 25),
    "Barcelona": (2, 6),
    "Paris": (1, 2),
    "Hamburg": (19, 22),
    "Tallinn": (11, 12)
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

# Function to check if a transition is valid
def is_valid_transition(city1, city2, day):
    return city2 in graph[city1] and (city2 not in fixed_events or fixed_events[city2][0] <= day <= fixed_events[city2][1])

# Function to find the next valid city to visit
def find_next_city(current_city, current_day, itinerary, visited_cities):
    for city in constraints.keys():
        if city not in visited_cities:
            if city in fixed_events:
                start, end = fixed_events[city]
                if start >= current_day and is_valid_transition(current_city, city, start):
                    return city, start, end - start + 1
            else:
                duration = constraints[city]
                if is_valid_transition(current_city, city, current_day):
                    return city, current_day, duration
    return None, None, None

# Function to create the itinerary
def create_itinerary():
    itinerary = []
    current_day = 1
    current_city = "Paris"  # Start from Paris as an example
    visited_cities = set(fixed_events.keys())  # Start with fixed events already considered
    
    # Add fixed events to the itinerary first
    for city, (start, end) in fixed_events.items():
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    
    # Sort itinerary by start day
    itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split()[1]))
    
    # Update current day based on the last fixed event
    if itinerary:
        last_event_end = int(itinerary[-1]['day_range'].split('-')[1].split()[1])
        current_day = last_event_end + 1
        current_city = itinerary[-1]['place']
    
    # Add remaining cities
    while current_day <= 25 and len(visited_cities) < len(constraints):
        next_city, start_day, duration = find_next_city(current_city, current_day, itinerary, visited_cities)
        
        if next_city is None:
            raise ValueError("Cannot satisfy all constraints")
        
        if next_city in fixed_events:
            start_day, end_day = fixed_events[next_city]
            duration = end_day - start_day + 1
        else:
            end_day = start_day + duration - 1
        
        if end_day > 25:
            raise ValueError("Itinerary exceeds 25 days")
        
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": next_city})
        visited_cities.add(next_city)
        current_day = end_day + 1
        current_city = next_city
    
    return itinerary

# Generate the itinerary
itinerary = create_itinerary()

# Output the result as JSON
print(json.dumps({"itinerary": itinerary}, indent=4))