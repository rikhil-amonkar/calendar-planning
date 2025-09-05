#!/usr/bin/env python3
import json
from collections import defaultdict

# Define the cities with their required durations (in days)
cities = {
    "Stockholm": 3,
    "Hamburg": 5,
    "Florence": 2,
    "Istanbul": 5,
    "Oslo": 5,
    "Vilnius": 5,
    "Santorini": 2,
    "Munich": 5,
    "Frankfurt": 4,
    "Krakow": 5
}

# Build the flight graph.
# For flights given as “A and B” we assume bidirectional.
# For those marked with “from X to Y” we allow only that direction.
def build_graph():
    graph = defaultdict(set)
    
    def add_bidirectional(a, b):
        graph[a].add(b)
        graph[b].add(a)
    
    def add_directed(a, b):
        graph[a].add(b)
    
    # Bidirectional flights:
    add_bidirectional("Oslo", "Stockholm")
    add_bidirectional("Krakow", "Frankfurt")
    add_bidirectional("Krakow", "Istanbul")
    add_bidirectional("Munich", "Stockholm")
    add_bidirectional("Hamburg", "Stockholm")
    add_bidirectional("Oslo", "Istanbul")
    add_bidirectional("Istanbul", "Stockholm")
    add_bidirectional("Oslo", "Krakow")
    add_bidirectional("Vilnius", "Istanbul")
    add_bidirectional("Oslo", "Vilnius")
    add_bidirectional("Frankfurt", "Istanbul")
    add_bidirectional("Oslo", "Frankfurt")
    add_bidirectional("Munich", "Hamburg")
    add_bidirectional("Munich", "Istanbul")
    add_bidirectional("Oslo", "Munich")
    add_bidirectional("Frankfurt", "Florence")
    add_bidirectional("Oslo", "Hamburg")
    add_bidirectional("Vilnius", "Frankfurt")
    add_bidirectional("Krakow", "Munich")
    add_bidirectional("Hamburg", "Istanbul")
    add_bidirectional("Frankfurt", "Stockholm")
    add_bidirectional("Frankfurt", "Munich")
    add_bidirectional("Krakow", "Stockholm")
    add_bidirectional("Frankfurt", "Hamburg")
    
    # Directed flights:
    add_directed("Krakow", "Vilnius")      # from Krakow to Vilnius
    add_directed("Florence", "Munich")      # from Florence to Munich
    add_directed("Stockholm", "Santorini")  # from Stockholm to Santorini
    add_directed("Santorini", "Oslo")       # from Santorini to Oslo
    add_directed("Vilnius", "Munich")       # from Vilnius to Munich
    
    return graph

graph = build_graph()

# Total trip days: 32, and note the sum of city durations is 41.
# Because if you fly on the same day (overlap) then total days = sum(durations) - (#transitions) = 41 - 9 = 32.

# Special event constraints:
# - Istanbul’s annual show must fall within its 5‐day stay. That forces the Istanbul segment to cover days 25–29.
#   In our model, if Istanbul is scheduled with start_day S then its days are [S, S + 5 - 1].
#   So for Istanbul we require S == 25.
# - The Krakow workshop must be attended between day 5 and day 9.
#   Thus if Krakow is scheduled with start_day S (and duration 5) its range is [S, S+4].
#   We require that [S, S+4] ∩ [5,9] is nonempty; a simple sufficient check is S <= 9.
    
# We'll use DFS/backtracking over all orderings. 
# The state maintained is a list of (city, start_day) tuples representing the itinerary so far.
# For a city added with start day X and duration d, the next city will start on day (X + d - 1).

solution = None

def dfs(path, used, current_day):
    global solution
    if solution is not None:
        return  # stop if solution already found
    if len(path) == len(cities):
        # At the end, the trip finishes on final_day = current_day + last city's duration - 1.
        # By design (41-9 = 32) it should always come to 32.
        solution = list(path)
        return

    # Try next candidate among the remaining cities.
    for city in cities:
        if city in used:
            continue
        
        # For non-initial segments, need to check flight from last city to candidate.
        if path:
            last_city, last_start = path[-1]
            if city not in graph[last_city]:
                continue  # no direct flight from last_city to this candidate
        
        # Check special scheduling constraints:
        # Istanbul must start exactly on day 25.
        if city == "Istanbul" and current_day != 25:
            continue
        # Krakow must start no later than day 9 (so that some day falls between day 5 and 9).
        if city == "Krakow" and current_day > 9:
            continue
        
        # Assign candidate a start day = current_day.
        new_start = current_day + cities[city] - 1  # next city's start day will be this
        # Place the candidate.
        path.append((city, current_day))
        used.add(city)
        dfs(path, used, new_start)
        if solution is not None:
            return
        # backtrack
        path.pop()
        used.remove(city)

# Start DFS. For the very first city, there's no flight constraint.
dfs([], set(), 1)

if solution is None:
    output = {"itinerary": []}
else:
    # Build itinerary list with day ranges.
    itinerary = []
    for city, start in solution:
        duration = cities[city]
        end = start + duration - 1
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    output = {"itinerary": itinerary}

# Output as JSON formatted dictionary.
print(json.dumps(output, indent=2))