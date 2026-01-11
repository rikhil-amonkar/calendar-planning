import json
from itertools import permutations

def main():
    # Cities and required days
    cities = {
        "Frankfurt": 4,
        "Salzburg": 5,
        "Athens": 5,
        "Reykjavik": 5,
        "Bucharest": 3,
        "Valencia": 2,
        "Vienna": 5,
        "Amsterdam": 3,
        "Stockholm": 3,
        "Riga": 3
    }
    
    # Direct flights (undirected)
    flights = [
        ("Valencia", "Frankfurt"),
        ("Vienna", "Bucharest"),
        ("Valencia", "Athens"),
        ("Athens", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Stockholm", "Athens"),
        ("Amsterdam", "Bucharest"),
        ("Athens", "Riga"),
        ("Amsterdam", "Frankfurt"),
        ("Stockholm", "Vienna"),
        ("Vienna", "Riga"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Frankfurt"),
        ("Stockholm", "Amsterdam"),
        ("Amsterdam", "Valencia"),
        ("Vienna", "Frankfurt"),
        ("Valencia", "Bucharest"),
        ("Bucharest", "Frankfurt"),
        ("Stockholm", "Frankfurt"),
        ("Valencia", "Vienna"),
        ("Reykjavik", "Athens"),
        ("Frankfurt", "Salzburg"),
        ("Amsterdam", "Vienna"),
        ("Stockholm", "Reykjavik"),
        ("Amsterdam", "Riga"),
        ("Stockholm", "Riga"),
        ("Vienna", "Reykjavik"),
        ("Amsterdam", "Athens"),
        ("Athens", "Frankfurt"),
        ("Vienna", "Athens"),
        ("Riga", "Bucharest")
    ]
    
    # Build adjacency set
    adj = {city: set() for city in cities}
    for a, b in flights:
        adj[a].add(b)
        adj[b].add(a)
    
    # Event constraints: city -> (start_day, end_day) must intersect given range
    event_constraints = [
        ("Stockholm", (1, 3)),
        ("Valencia", (5, 6)),
        ("Vienna", (6, 10)),
        ("Athens", (14, 18)),
        ("Riga", (18, 20))
    ]
    
    # Search over permutations
    city_names = list(cities.keys())
    
    def check_sequence(seq):
        # Check direct flights
        for i in range(len(seq) - 1):
            if seq[i+1] not in adj[seq[i]]:
                return False
        
        # Compute start days
        start_days = [0] * len(seq)
        start_days[0] = 1
        for i in range(1, len(seq)):
            start_days[i] = start_days[i-1] + cities[seq[i-1]] - 1
        
        # Check event constraints
        for city, (event_start, event_end) in event_constraints:
            idx = seq.index(city)
            city_start = start_days[idx]
            city_end = city_start + cities[city] - 1
            # Overlap check
            if not (city_start <= event_end and city_end >= event_start):
                return False
        
        # Also total trip length check (should be 29 automatically if all cities visited once)
        trip_length = start_days[-1] + cities[seq[-1]] - 1
        if trip_length != 29:
            return False
        
        return (start_days, trip_length)
    
    # Try permutations (10! is large, but we can break early if found)
    # For speed, we might need heuristic, but let's try brute force with pruning.
    # We'll do DFS for better pruning.
    
    found_seq = None
    found_starts = None
    
    def dfs(seq, remaining):
        nonlocal found_seq, found_starts
        if found_seq:
            return
        if not remaining:
            res = check_sequence(seq)
            if res:
                found_seq = seq[:]
                found_starts = res[0]
            return
        
        # Prune: check adjacency for last in seq
        if len(seq) > 0:
            last = seq[-1]
            possible_next = [c for c in remaining if c in adj[last]]
        else:
            possible_next = remaining
        
        for city in possible_next:
            dfs(seq + [city], [c for c in remaining if c != city])
    
    dfs([], city_names)
    
    if not found_seq:
        print('{"itinerary": []}')
        return
    
    # Build itinerary for output
    itinerary = []
    for i, city in enumerate(found_seq):
        start = found_starts[i]
        end = start + cities[city] - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()