import json

# Set up city durations
durations = {
    "Oslo": 2,
    "Helsinki": 2,
    "Edinburgh": 3,
    "Riga": 2,
    "Tallinn": 5,
    "Budapest": 5,
    "Vilnius": 5,
    "Porto": 5,
    "Geneva": 4
}

cities = list(durations.keys())

# Build the flight graph as an undirected graph.
# Each tuple represents a direct flight (bidirectional).
edges = [
    ("Porto", "Oslo"),
    ("Edinburgh", "Budapest"),
    ("Edinburgh", "Geneva"),
    ("Riga", "Tallinn"),
    ("Edinburgh", "Porto"),
    ("Vilnius", "Helsinki"),
    ("Tallinn", "Vilnius"),   # originally "from Tallinn to Vilnius"
    ("Riga", "Oslo"),
    ("Geneva", "Oslo"),
    ("Edinburgh", "Oslo"),
    ("Edinburgh", "Helsinki"),
    ("Vilnius", "Oslo"),
    ("Riga", "Helsinki"),
    ("Budapest", "Geneva"),
    ("Helsinki", "Budapest"),
    ("Helsinki", "Oslo"),
    ("Edinburgh", "Riga"),
    ("Tallinn", "Helsinki"),
    ("Geneva", "Porto"),
    ("Budapest", "Oslo"),
    ("Helsinki", "Geneva"),
    ("Riga", "Vilnius"),
    ("Tallinn", "Oslo")
]

# Create graph dictionary
graph = {city: set() for city in cities}
for city1, city2 in edges:
    graph[city1].add(city2)
    graph[city2].add(city1)

# Total number of cities to visit
TOTAL_CITIES = len(cities)

# The DFS function will attempt to find an itinerary (a Hamiltonian path)
# that satisfies the flight connectivity and the special time constraints.
# We pass along the current path and the cumulative sum of durations so far.
# The next city's start day is computed as: start = 1 + (cumulative_duration) - (len(path))
# (Because the first city always starts on day 1, and each transition overlaps one day)
def dfs(path, cumulative):
    if len(path) == TOTAL_CITIES:
        # Found a full itinerary; no further check needed here since we pruned special city constraints along the way.
        return path

    # Determine candidates:
    if not path:
        # If no city chosen yet, try any city.
        candidates = [c for c in cities]
    else:
        # Next candidate must be directly connected to the current city.
        last = path[-1]
        remaining = set(cities) - set(path)
        candidates = [c for c in graph[last] if c in remaining]

    # Try each candidate.
    for candidate in candidates:
        # Compute the start day for the candidate:
        # For a path of length n, the candidate will be at position n (0-indexed)
        # and its start day is: 1 + (sum of durations of cities already in path) - (number of transitions = len(path))
        next_start = 1 + cumulative - len(path)
        # Special constraint for Tallinn (wedding in Tallinn between day 4 and 8)
        # Tallinn's 5-day block must intersect [4,8]; a sufficient check is that its start day is <= 8.
        if candidate == "Tallinn" and next_start > 8:
            continue
        # Special constraint for Oslo (friend meeting between day 24 and 25) 
        # Oslo's 2-day block [S, S+1] must cover day 24 or 25.
        # This implies the start day S must be either 23 (block 23-24) or 24 (block 24-25).
        if candidate == "Oslo" and not (23 <= next_start <= 24):
            continue

        # Choose candidate and update cumulative duration.
        new_path = path + [candidate]
        new_cumulative = cumulative + durations[candidate]
        result = dfs(new_path, new_cumulative)
        if result is not None:
            return result

    return None

# Find a valid itinerary ordering.
itinerary_order = dfs([], 0)

if itinerary_order is None:
    result = {"error": "No valid itinerary found with the given constraints."}
else:
    # Build the day itinerary.
    # For city at index i, its start day = 1 + sum(durations of all previous cities) - i
    schedule = []
    cumulative = 0
    for i, city in enumerate(itinerary_order):
        start_day = 1 + cumulative - i
        end_day = start_day + durations[city] - 1
        schedule.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        cumulative += durations[city]
    result = {"itinerary": schedule}

# Output the result in JSON format.
print(json.dumps(result))