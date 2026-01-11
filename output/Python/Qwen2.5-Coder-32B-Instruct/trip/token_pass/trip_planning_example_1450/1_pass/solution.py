import json
from collections import defaultdict

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
    "Krakow": 5,
    "events": {
        "Krakow_workshop": (5, 9),
        "Istanbul_show": (25, 29)
    }
}

# Define the flight connections
flight_connections = [
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

# Convert flight connections to a graph
graph = defaultdict(list)
for u, v in flight_connections:
    graph[u].append(v)
    graph[v].append(u)

# Initialize the itinerary
itinerary = []
days_used = 0

# Add mandatory events
def add_event(event_name, start_day, end_day):
    global days_used
    if event_name == "Krakow_workshop":
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Krakow"})
        days_used += (end_day - start_day + 1)
    elif event_name == "Istanbul_show":
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Istanbul"})
        days_used += (end_day - start_day + 1)

add_event("Krakow_workshop", 5, 9)
add_event("Istanbul_show", 25, 29)

# Add cities with fixed durations
def add_city(city, duration):
    global days_used
    itinerary.append({"day_range": f"Day {days_used+1}-{days_used+duration}", "place": city})
    days_used += duration

add_city("Stockholm", 3)
add_city("Hamburg", 5)
add_city("Florence", 2)
add_city("Oslo", 5)
add_city("Vilnius", 5)
add_city("Santorini", 2)
add_city("Munich", 5)
add_city("Frankfurt", 4)

# Function to check if a transition is possible
def can_transition(from_city, to_city, current_day):
    return to_city in graph[from_city] and current_day + 1 <= 32

# Add remaining cities with flexible durations
def add_remaining_cities():
    global days_used
    cities_to_add = ["Krakow", "Istanbul"]
    for city in cities_to_add:
        if city == "Krakow":
            # Krakow is already added for the workshop, but we need to ensure full duration
            if days_used < 9:
                days_needed = 9 - days_used
                itinerary.append({"day_range": f"Day {days_used+1}-{days_used+days_needed}", "place": "Krakow"})
                days_used += days_needed
            if days_used < 14:
                days_needed = 14 - days_used
                itinerary.append({"day_range": f"Day {days_used+1}-{days_used+days_needed}", "place": "Krakow"})
                days_used += days_needed
        elif city == "Istanbul":
            # Istanbul is already added for the show, but we need to ensure full duration
            if days_used < 29:
                days_needed = 29 - days_used
                itinerary.append({"day_range": f"Day {days_used+1}-{days_used+days_needed}", "place": "Istanbul"})
                days_used += days_needed
            if days_used < 32:
                days_needed = 32 - days_used
                itinerary.append({"day_range": f"Day {days_used+1}-{days_used+days_needed}", "place": "Istanbul"})
                days_used += days_needed

add_remaining_cities()

# Sort the itinerary by day range
itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

# Output the itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))