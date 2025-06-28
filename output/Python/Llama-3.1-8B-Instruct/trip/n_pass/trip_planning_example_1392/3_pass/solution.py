import json
import networkx as nx
from collections import defaultdict

# Define the trip constraints
cities = {
    "Naples": 3,
    "Valencia": 5,
    "Stuttgart": 2,
    "Split": 5,
    "Venice": 5,
    "Amsterdam": 4,
    "Nice": 2,
    "Barcelona": 2,
    "Porto": 4
}

flights = {
    ("Venice", "Nice"),
    ("Naples", "Amsterdam"),
    ("Barcelona", "Nice"),
    ("Amsterdam", "Nice"),
    ("Stuttgart", "Valencia"),
    ("Stuttgart", "Porto"),
    ("Split", "Stuttgart"),
    ("Split", "Naples"),
    ("Valencia", "Amsterdam"),
    ("Barcelona", "Porto"),
    ("Valencia", "Naples"),
    ("Venice", "Amsterdam"),
    ("Barcelona", "Naples"),
    ("Barcelona", "Valencia"),
    ("Split", "Amsterdam"),
    ("Barcelona", "Venice"),
    ("Stuttgart", "Amsterdam"),
    ("Naples", "Nice"),
    ("Venice", "Stuttgart"),
    ("Split", "Barcelona"),
    ("Porto", "Nice"),
    ("Barcelona", "Stuttgart"),
    ("Venice", "Naples"),
    ("Porto", "Amsterdam"),
    ("Porto", "Valencia"),
    ("Stuttgart", "Naples"),
    ("Barcelona", "Amsterdam")
}

constraints = {
    "Naples": [(18, 20)],
    "Barcelona": [(5, 6)],
    "Venice": [(6, 10)]
}

# Create a directed graph
G = nx.DiGraph()

# Add edges to the graph
for city1, city2 in flights:
    G.add_edge(city1, city2)

# Perform a depth-first search to find a valid itinerary
def dfs(current_city, remaining_days, visited_cities, itinerary):
    if remaining_days == 0:
        return True
    for city in G.neighbors(current_city):
        if city not in visited_cities:
            visited_cities.add(city)
            if dfs(city, remaining_days - cities[city], visited_cities, itinerary):
                itinerary.append({"day_range": f"Day {len(itinerary) + 1}-{len(itinerary) + cities[city]}", "place": city})
                return True
            visited_cities.remove(city)
    return False

# Find a valid itinerary
itinerary = []
visited_cities = set()
days = 0
dfs("Naples", 24, visited_cities, itinerary)

# Apply constraints
for city, constraint_days in constraints.items():
    for start_day, end_day in constraint_days:
        for i, entry in enumerate(itinerary):
            if entry["place"] == city:
                start_day_index = i + start_day - 1
                end_day_index = i + end_day
                itinerary[start_day_index]["day_range"] = f"Day {start_day}-{end_day}"
                for j in range(start_day_index + 1, end_day_index):
                    itinerary[j]["place"] = city
                break

# Adjust the day ranges to ensure the itinerary covers exactly 24 days
total_days = 0
for entry in itinerary:
    start_day, end_day = map(int, entry["day_range"].split("-"))
    total_days += end_day - start_day + 1

# If the itinerary covers more than 24 days, remove the excess days
if total_days > 24:
    excess_days = total_days - 24
    for i in range(len(itinerary) - 1, -1, -1):
        start_day, end_day = map(int, itinerary[i]["day_range"].split("-"))
        if excess_days > 0:
            itinerary[i]["day_range"] = f"Day {end_day - excess_days + 1}-{end_day}"
            excess_days -= end_day - start_day + 1

# If the itinerary covers less than 24 days, add the required days
elif total_days < 24:
    days_to_add = 24 - total_days
    for i in range(len(itinerary) - 1, -1, -1):
        start_day, end_day = map(int, itinerary[i]["day_range"].split("-"))
        if days_to_add > 0:
            itinerary[i]["day_range"] = f"Day {start_day}-{start_day + min(days_to_add, end_day - start_day + 1)}"
            days_to_add -= min(days_to_add, end_day - start_day + 1)

# Output the result as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))