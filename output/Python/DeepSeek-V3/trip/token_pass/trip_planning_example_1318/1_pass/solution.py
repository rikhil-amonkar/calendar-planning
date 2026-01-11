import json
from itertools import permutations

# Cities and required days
req = {
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

# Direct flights graph (bidirectional)
edges = [
    ("Porto", "Oslo"),
    ("Edinburgh", "Budapest"),
    ("Edinburgh", "Geneva"),
    ("Riga", "Tallinn"),
    ("Edinburgh", "Porto"),
    ("Vilnius", "Helsinki"),
    ("Tallinn", "Vilnius"),
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

# Make adjacency list
adj = {city: set() for city in req}
for a, b in edges:
    adj[a].add(b)
    adj[b].add(a)

# Fixed constraints: Tallinn days 4-8, Oslo days 24-25
def satisfies_fixed(itinerary):
    # itinerary: list of (city, start_day, end_day inclusive)
    tallinn_ok = False
    oslo_ok = False
    for city, start, end in itinerary:
        if city == "Tallinn":
            if start <= 4 and end >= 8:
                # Check if fully covers 4-8
                # Actually, we need exactly 4-8 in Tallinn, but can have extra at edges due to travel
                # For simplicity, check if 4,5,6,7,8 are within start..end
                if all(start <= d <= end for d in [4,5,6,7,8]):
                    tallinn_ok = True
        if city == "Oslo":
            if start <= 24 and end >= 25:
                if all(start <= d <= end for d in [24, 25]):
                    oslo_ok = True
    return tallinn_ok and oslo_ok

# Search
def dfs(current_city, current_day, visited_days, itinerary, solutions):
    if current_day > 25:
        return
    if current_day == 25:
        # Check if all requirements met
        if all(visited_days[city] == req[city] for city in req):
            if satisfies_fixed(itinerary):
                solutions.append(itinerary.copy())
        return
    
    # Try staying in current city for 1..n days
    max_stay = 25 - current_day
    for stay in range(1, max_stay + 1):
        new_day = current_day + stay
        # Update visited days for current city
        visited_days[current_city] += stay
        itinerary.append((current_city, current_day, new_day - 1))
        
        if new_day == 25:
            # End of trip
            dfs(current_city, new_day, visited_days, itinerary, solutions)
        else:
            # Travel to next city
            for next_city in adj[current_city]:
                # Travel day counts for both cities
                visited_days[next_city] += 1
                dfs(next_city, new_day + 1, visited_days, itinerary, solutions)
                visited_days[next_city] -= 1
        
        # Backtrack
        itinerary.pop()
        visited_days[current_city] -= stay

# Run search from each starting city
solutions = []
for start_city in req:
    visited_days = {city: 0 for city in req}
    dfs(start_city, 1, visited_days, [], solutions)

# Take first solution
if solutions:
    sol = solutions[0]
    # Convert to required JSON format
    itinerary_json = []
    for city, start, end in sol:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_json.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary_json}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))