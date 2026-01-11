import json
from collections import defaultdict

# Define the cities and their direct flight connections
cities = [
    ("Munich", "Vienna"), ("Istanbul", "Brussels"), ("Vienna", "Vilnius"),
    ("Madrid", "Munich"), ("Venice", "Brussels"), ("Riga", "Brussels"),
    ("Geneva", "Istanbul"), ("Munich", "Reykjavik"), ("Vienna", "Istanbul"),
    ("Riga", "Istanbul"), ("Reykjavik", "Vienna"), ("Venice", "Munich"),
    ("Madrid", "Venice"), ("Vilnius", "Istanbul"), ("Venice", "Vienna"),
    ("Venice", "Istanbul"), ("Reykjavik", "Madrid"), ("Riga", "Munich"),
    ("Munich", "Istanbul"), ("Reykjavik", "Brussels"), ("Vilnius", "Brussels"),
    ("Vilnius", "Munich"), ("Madrid", "Vienna"), ("Vienna", "Riga"),
    ("Geneva", "Vienna"), ("Madrid", "Brussels"), ("Vienna", "Brussels"),
    ("Geneva", "Brussels"), ("Geneva", "Madrid"), ("Munich", "Brussels"),
    ("Madrid", "Istanbul"), ("Geneva", "Munich"), ("Riga", "Vilnius")
]

# Create a graph from the cities and their connections
graph = defaultdict(list)
for city1, city2 in cities:
    graph[city1].append(city2)
    graph[city2].append(city1)

# Define the constraints
constraints = {
    "Istanbul": (4, [None, None]),  # 4 days, no specific days
    "Vienna": (4, [None, None]),   # 4 days, no specific days
    "Riga": (2, [None, None]),     # 2 days, no specific days
    "Brussels": (2, [26, 27]),     # 2 days, must be between day 26 and 27
    "Madrid": (4, [None, None]),   # 4 days, no specific days
    "Vilnius": (4, [20, 23]),      # 4 days, must be between day 20 and 23
    "Venice": (5, [7, 11]),        # 5 days, must be between day 7 and 11
    "Geneva": (4, [1, 4]),         # 4 days, must be between day 1 and 4
    "Munich": (5, [None, None]),   # 5 days, no specific days
    "Reykjavik": (2, [None, None]) # 2 days, no specific days
}

# Function to check if a city can be visited on a given day
def can_visit(city, day, itinerary):
    for entry in itinerary:
        start, end = map(int, entry['day_range'].split('-')[0][4:]), map(int, entry['day_range'].split('-')[1])
        if start <= day <= end and entry['place'] != city:
            return False
    return True

# Function to find a valid day to start visiting a city
def find_start_day(city, required_days, fixed_start, fixed_end, itinerary):
    if fixed_start is not None:
        return fixed_start
    for day in range(1, 28 - required_days + 1):
        if can_visit(city, day, itinerary):
            return day
    return None

# Initialize the itinerary
itinerary = []

# Process constraints in order of priority (fixed days first)
sorted_constraints = sorted(constraints.items(), key=lambda x: x[1][1] is not None)

for city, (required_days, (fixed_start, fixed_end)) in sorted_constraints:
    start_day = find_start_day(city, required_days, fixed_start, fixed_end, itinerary)
    if start_day is None:
        raise ValueError(f"Cannot find a valid start day for {city}")
    
    # Check connectivity
    last_city = None if not itinerary else itinerary[-1]['place']
    if last_city and city not in graph[last_city]:
        # Find a path to connect to the last city
        visited = set()
        stack = [(last_city, [])]
        while stack:
            current, path = stack.pop()
            if current == city:
                break
            for neighbor in graph[current]:
                if neighbor not in visited:
                    visited.add(neighbor)
                    stack.append((neighbor, path + [neighbor]))
        else:
            raise ValueError(f"No valid path to connect {last_city} to {city}")
        
        # Add intermediate cities to the itinerary
        for intermediate_city in path:
            if not any(entry['place'] == intermediate_city for entry in itinerary):
                itinerary.append({"day_range": f"Day {start_day}-{start_day}", "place": intermediate_city})
                start_day += 1
    
    # Add the current city to the itinerary
    itinerary.append({"day_range": f"Day {start_day}-{start_day + required_days - 1}", "place": city})

# Output the itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))