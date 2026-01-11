import json
from itertools import permutations

# Direct flights graph
direct_flights = {
    'Bucharest': ['Vienna', 'Riga', 'Istanbul', 'Manchester'],
    'Vienna': ['Bucharest', 'Reykjavik', 'Manchester', 'Riga', 'Istanbul', 'Florence', 'Stuttgart'],
    'Reykjavik': ['Vienna', 'Stuttgart'],
    'Manchester': ['Vienna', 'Riga', 'Istanbul', 'Bucharest', 'Stuttgart'],
    'Riga': ['Vienna', 'Manchester', 'Bucharest', 'Istanbul'],
    'Istanbul': ['Vienna', 'Riga', 'Stuttgart', 'Bucharest', 'Manchester'],
    'Florence': ['Vienna'],
    'Stuttgart': ['Vienna', 'Istanbul', 'Reykjavik', 'Manchester']
}

# Desired days (preferences)
desired_days = {
    'Riga': 4,
    'Manchester': 5,
    'Bucharest': 4,
    'Florence': 4,
    'Vienna': 2,
    'Istanbul': 2,
    'Reykjavik': 4,
    'Stuttgart': 5
}

# Fixed constraints
fixed_events = {
    'Bucharest': [(16, 19)],  # days 16-19 inclusive
    'Istanbul': [(12, 13)]    # days 12-13 inclusive
}

total_days = 23
cities = list(desired_days.keys())

# Helper: check if two cities are connected
def connected(c1, c2):
    return c2 in direct_flights[c1]

# Generate possible day allocations for 8 cities, each at least 1 day, sum = 23
# But we also have fixed days for Bucharest and Istanbul
# We'll search over sequences of cities (with possible repeats) and durations

def dfs(path, durations, day, used_cities, results):
    # path: list of city names visited so far
    # durations: list of days spent in each city in path
    # day: current day number (1-based) after last visit
    # used_cities: set of cities visited so far
    if day > total_days:
        return
    if day == total_days:
        if len(used_cities) == 8:
            # Check fixed events
            # Build day mapping
            day_to_city = {}
            idx = 0
            current_day = 1
            for i in range(len(path)):
                city = path[i]
                dur = durations[i]
                for d in range(current_day, current_day + dur):
                    day_to_city[d] = city
                current_day += dur
            # Check Bucharest days 16-19
            ok = True
            for d in range(16, 20):
                if day_to_city.get(d) != 'Bucharest':
                    ok = False
                    break
            if ok:
                # Check Istanbul days 12-13
                if day_to_city.get(12) == 'Istanbul' and day_to_city.get(13) == 'Istanbul':
                    # Check connectivity
                    connect_ok = True
                    for i in range(len(path)-1):
                        if not connected(path[i], path[i+1]):
                            connect_ok = False
                            break
                    if connect_ok:
                        results.append((list(path), list(durations)))
        return
    
    # Prune: if remaining days < cities not yet visited, impossible
    remaining_cities = 8 - len(used_cities)
    if total_days - day < remaining_cities:
        return
    
    # Try to stay longer in current city or move to new city
    current_city = path[-1] if path else None
    # Option 1: extend stay in current city
    if path:
        durations[-1] += 1
        dfs(path, durations, day + 1, used_cities, results)
        durations[-1] -= 1
    
    # Option 2: move to a new city (connected)
    if current_city is None:
        # Start from any city
        for city in cities:
            dfs([city], [1], day + 1, {city}, results)
    else:
        for next_city in cities:
            if next_city == current_city:
                continue
            if not connected(current_city, next_city):
                continue
            new_used = set(used_cities)
            new_used.add(next_city)
            dfs(path + [next_city], durations + [1], day + 1, new_used, results)

# Run search
results = []
dfs([], [], 0, set(), results)

if not results:
    print(json.dumps({"itinerary": []}))
else:
    # Pick first valid result
    path, durations = results[0]
    # Convert to day ranges
    itinerary = []
    current_day = 1
    for i in range(len(path)):
        start = current_day
        end = current_day + durations[i] - 1
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": path[i]})
        current_day += durations[i]
    
    print(json.dumps({"itinerary": itinerary}, indent=2))