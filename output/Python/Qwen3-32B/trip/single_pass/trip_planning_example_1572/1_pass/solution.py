import json
from itertools import permutations

# Define cities and their required durations
cities = {
    'Berlin': 2,
    'Paris': 5,
    'Lyon': 3,
    'Milan': 3,
    'Riga': 2,
    'Nice': 2,
    'Seville': 3,
    'Naples': 4,
    'Zurich': 5,
    'Stockholm': 3,
}

# Define direct flights as a set of unordered pairs
direct_flights = {
    frozenset({'Paris', 'Stockholm'}),
    frozenset({'Seville', 'Paris'}),
    frozenset({'Naples', 'Zurich'}),
    frozenset({'Nice', 'Riga'}),
    frozenset({'Berlin', 'Milan'}),
    frozenset({'Paris', 'Zurich'}),
    frozenset({'Paris', 'Nice'}),
    frozenset({'Milan', 'Paris'}),
    frozenset({'Milan', 'Riga'}),
    frozenset({'Paris', 'Lyon'}),
    frozenset({'Milan', 'Naples'}),
    frozenset({'Paris', 'Riga'}),
    frozenset({'Berlin', 'Stockholm'}),
    frozenset({'Stockholm', 'Riga'}),
    frozenset({'Nice', 'Zurich'}),
    frozenset({'Milan', 'Zurich'}),
    frozenset({'Lyon', 'Nice'}),
    frozenset({'Zurich', 'Stockholm'}),
    frozenset({'Zurich', 'Riga'}),
    frozenset({'Berlin', 'Naples'}),
    frozenset({'Milan', 'Stockholm'}),
    frozenset({'Berlin', 'Zurich'}),
    frozenset({'Milan', 'Seville'}),
    frozenset({'Paris', 'Naples'}),
    frozenset({'Berlin', 'Riga'}),
    frozenset({'Nice', 'Stockholm'}),
    frozenset({'Berlin', 'Paris'}),
    frozenset({'Nice', 'Naples'}),
    frozenset({'Berlin', 'Nice'}),
}

# Convert to adjacency list for easier access
flight_graph = {city: [] for city in cities}
for flight in direct_flights:
    a, b = flight
    flight_graph[a].append(b)
    flight_graph[b].append(a)

# Function to check if a path is valid (direct flights between consecutive cities)
def is_valid_path(path):
    for i in range(len(path) - 1):
        current = path[i]
        next_city = path[i + 1]
        if next_city not in flight_graph[current]:
            return False
    return True

# Function to calculate day ranges for each city in the path
def calculate_day_ranges(path):
    day_ranges = []
    current_day = 1
    for city in path:
        duration = cities[city]
        end_day = current_day + duration - 1
        day_ranges.append((city, current_day, end_day))
        current_day = end_day + 1  # Next city starts on the end day of the previous
    return day_ranges

# Function to check if the path satisfies all event constraints
def satisfies_constraints(day_ranges):
    # Check Berlin starts on day 1
    berlin_start = day_ranges[0][1]
    if berlin_start != 1:
        return False
    
    # Find Nice's days
    nice_days = None
    for city, start, end in day_ranges:
        if city == 'Nice':
            nice_days = (start, end)
            break
    if not nice_days or not (12 <= nice_days[0] and nice_days[1] >= 13):
        return False
    
    # Find Stockholm's days
    stockholm_days = None
    for city, start, end in day_ranges:
        if city == 'Stockholm':
            stockholm_days = (start, end)
            break
    if not stockholm_days or not (20 <= stockholm_days[0] and stockholm_days[1] >= 22):
        return False
    
    return True

# Try all permutations starting with Berlin
city_list = list(cities.keys())
for perm in permutations(city_list):
    if perm[0] != 'Berlin':
        continue
    if is_valid_path(perm):
        day_ranges = calculate_day_ranges(perm)
        if satisfies_constraints(day_ranges):
            # Construct the itinerary
            itinerary = []
            for city, start, end in day_ranges:
                day_range_str = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range_str, "place": city})
            print(json.dumps({"itinerary": itinerary}))
            break