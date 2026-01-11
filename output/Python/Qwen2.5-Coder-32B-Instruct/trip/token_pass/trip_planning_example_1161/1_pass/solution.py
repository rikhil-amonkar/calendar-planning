import json
from collections import defaultdict

# Define the constraints
cities_duration = {
    "Mykonos": 4,
    "Krakow": 5,
    "Vilnius": 2,
    "Helsinki": 2,
    "Dubrovnik": 3,
    "Oslo": 2,
    "Madrid": 5,
    "Paris": 2
}

fixed_events = {
    "Mykonos": (15, 18),
    "Dubrovnik": (2, 4),
    "Oslo": (1, 2)
}

# Define the available direct flights as a graph
flights = [
    ("Oslo", "Krakow"), ("Oslo", "Paris"), ("Paris", "Madrid"),
    ("Helsinki", "Vilnius"), ("Oslo", "Madrid"), ("Oslo", "Helsinki"),
    ("Helsinki", "Krakow"), ("Dubrovnik", "Helsinki"), ("Dubrovnik", "Madrid"),
    ("Oslo", "Dubrovnik"), ("Krakow", "Paris"), ("Madrid", "Mykonos"),
    ("Oslo", "Vilnius"), ("Krakow", "Vilnius"), ("Helsinki", "Paris"),
    ("Vilnius", "Paris"), ("Helsinki", "Madrid")
]

# Create adjacency list for the graph
graph = defaultdict(list)
for u, v in flights:
    graph[u].append(v)
    graph[v].append(u)

def find_itinerary():
    itinerary = []
    current_day = 1
    visited_cities = set()

    # Schedule fixed events first
    for city, (start_day, end_day) in fixed_events.items():
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        visited_cities.add(city)
        current_day = end_day + 1

    # Sort cities by priority based on remaining days and duration
    remaining_cities = [(city, duration) for city, duration in cities_duration.items() if city not in visited_cities]
    remaining_cities.sort(key=lambda x: x[1], reverse=True)

    # Greedily fill the remaining days
    while remaining_cities and current_day <= 18:
        for i, (city, duration) in enumerate(remaining_cities):
            # Check if we can fit this city in the remaining days
            if current_day + duration - 1 <= 18:
                # Check if there's a flight from the last city in the itinerary to this city
                if not itinerary or any(flight_city in graph[itinerary[-1]['place']] for flight_city in [city] + graph[city]):
                    itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
                    visited_cities.add(city)
                    current_day += duration
                    remaining_cities.pop(i)
                    break

    return itinerary

itinerary = find_itinerary()
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))