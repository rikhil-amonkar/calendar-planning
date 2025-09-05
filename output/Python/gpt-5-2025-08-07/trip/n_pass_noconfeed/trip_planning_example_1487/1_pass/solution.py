import json
from itertools import permutations

def main():
    # Input variables and constraints
    total_days = 28
    cities = [
        "Copenhagen", "Geneva", "Mykonos", "Naples", "Prague",
        "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"
    ]
    required_cities_count = 10  # Must visit all 10 cities
    
    # Durations per city (days). Note: total sum is 37; with 9 flights (overlap days) -> 28 unique days.
    durations = {
        "Copenhagen": 5,
        "Geneva": 3,
        "Mykonos": 2,
        "Naples": 4,
        "Prague": 2,
        "Dubrovnik": 3,
        "Athens": 4,
        "Santorini": 5,
        "Brussels": 4,
        "Munich": 5
    }
    
    # Windows constraints: city must include at least one day in the [start, end] window.
    windows_any = {
        "Copenhagen": (11, 15),  # meet friend
        "Naples": (5, 8),        # visit relatives
        "Athens": (8, 11)        # workshop
    }
    # Must include all of these exact days
    windows_must_days = {
        "Mykonos": {27, 28}      # conference
    }
    
    # Direct flights (undirected)
    flight_pairs = [
        ("Copenhagen", "Dubrovnik"),
        ("Brussels", "Copenhagen"),
        ("Prague", "Geneva"),
        ("Athens", "Geneva"),
        ("Naples", "Dubrovnik"),
        ("Athens", "Dubrovnik"),
        ("Geneva", "Mykonos"),
        ("Naples", "Mykonos"),
        ("Naples", "Copenhagen"),
        ("Munich", "Mykonos"),
        ("Naples", "Athens"),
        ("Prague", "Athens"),
        ("Santorini", "Geneva"),
        ("Athens", "Santorini"),
        ("Naples", "Munich"),
        ("Prague", "Copenhagen"),
        ("Brussels", "Naples"),
        ("Athens", "Mykonos"),
        ("Athens", "Copenhagen"),
        ("Naples", "Geneva"),
        ("Dubrovnik", "Munich"),
        ("Brussels", "Munich"),
        ("Prague", "Brussels"),
        ("Brussels", "Athens"),
        ("Athens", "Munich"),
        ("Geneva", "Munich"),
        ("Copenhagen", "Munich"),
        ("Brussels", "Geneva"),
        ("Copenhagen", "Geneva"),
        ("Prague", "Munich"),
        ("Copenhagen", "Santorini"),
        ("Naples", "Santorini"),
        ("Geneva", "Dubrovnik")
    ]
    
    # Build adjacency map
    adj = {c: set() for c in cities}
    for a, b in flight_pairs:
        if a in adj and b in adj:
            adj[a].add(b)
            adj[b].add(a)
    
    # Helper to compute day ranges from an ordered list of cities
    def compute_ranges(order):
        # order is a list of all 10 cities in visiting sequence
        ranges = {}
        current_start = 1
        for i, city in enumerate(order):
            s = current_start
            e = s + durations[city] - 1
            ranges[city] = (s, e)
            current_start = e  # overlap on flight day
        return ranges
    
    def intersects(r1, r2):
        a1, b1 = r1
        a2, b2 = r2
        return not (b1 < a2 or b2 < a1)
    
    def check_windows(ranges):
        # windows_any
        for city, (ws, we) in windows_any.items():
            if city not in ranges:
                return False
            s, e = ranges[city]
            if not intersects((s, e), (ws, we)):
                return False
        # windows_must_days
        for city, days in windows_must_days.items():
            if city not in ranges:
                return False
            s, e = ranges[city]
            for d in days:
                if not (s <= d <= e):
                    return False
        return True
    
    def check_adjacency(order):
        for i in range(len(order) - 1):
            if order[i+1] not in adj[order[i]]:
                return False
        return True
    
    # We enforce Mykonos as the last city so days 27-28 are Mykonos (given durations sum and overlaps)
    last_city = "Mykonos"
    cities_wo_mykonos = [c for c in cities if c != last_city]
    
    # Heuristic: order candidates by window start day (earlier windows first), then alphabetically
    def sort_key(city):
        if city in windows_any:
            return (windows_any[city][0], city)
        else:
            return (10**9, city)
    base_candidates = sorted(cities_wo_mykonos, key=sort_key)
    
    # Backtracking DFS to find a valid sequence
    best_order = None
    
    def dfs(order, used, next_start):
        nonlocal best_order
        if best_order is not None:
            return  # already found one
        
        if len(order) == len(cities_wo_mykonos):
            # Check final hop to Mykonos is direct
            if order and last_city not in adj[order[-1]]:
                return
            final_order = order + [last_city]
            ranges = compute_ranges(final_order)
            # Validate end day equals total_days
            end_day = ranges[final_order[-1]][1]
            if end_day != total_days:
                return
            # Check all windows
            if not check_windows(ranges):
                return
            # Full adjacency check (should pass)
            if not check_adjacency(final_order):
                return
            best_order = final_order
            return
        
        # Choose next city by heuristic: remaining candidates sorted by sort_key
        remaining = [c for c in base_candidates if c not in used]
        for city in remaining:
            # Check adjacency to previous city
            if order:
                prev = order[-1]
                if city not in adj[prev]:
                    continue
            # Compute this city's tentative range
            s = 1 if not order else next_start
            e = s + durations[city] - 1
            
            # Early window pruning for this city if it has a window
            if city in windows_any:
                ws, we = windows_any[city]
                if not intersects((s, e), (ws, we)):
                    continue
            
            # Also prune if city has must-include days (none for the 9, Mykonos is last)
            if city in windows_must_days:
                days = windows_must_days[city]
                if not all(s <= d <= e for d in days):
                    continue
            
            # Additional soft pruning: ensure that the last city before Mykonos can connect to Mykonos.
            # If placing this city would end up as the last before Mykonos, check adjacency:
            if len(order) + 1 == len(cities_wo_mykonos):
                if last_city not in adj[city]:
                    continue
            
            used.add(city)
            order.append(city)
            dfs(order, used, e)
            order.pop()
            used.remove(city)
    
    dfs([], set(), 1)
    
    # If no plan found (should not happen), return an error JSON
    if best_order is None:
        print(json.dumps({"itinerary": [], "error": "No valid itinerary found with given constraints"}))
        return
    
    # Build final itinerary output
    ranges = compute_ranges(best_order)
    itinerary = []
    for city in best_order:
        s, e = ranges[city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()