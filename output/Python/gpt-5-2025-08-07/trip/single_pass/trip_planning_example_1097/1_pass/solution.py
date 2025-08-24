import itertools
import json

def build_adjacency():
    adj = {}
    def add_city(c):
        if c not in adj:
            adj[c] = set()
    def add_edge(a, b, bidirectional=True):
        add_city(a); add_city(b)
        adj[a].add(b)
        if bidirectional:
            adj[b].add(a)
    # Build adjacency based on provided direct flights
    add_edge("Warsaw", "Reykjavik", True)
    add_edge("Oslo", "Madrid", True)
    add_edge("Warsaw", "Riga", True)
    add_edge("Lyon", "London", True)
    add_edge("Madrid", "London", True)
    add_edge("Warsaw", "London", True)
    add_edge("Reykjavik", "Madrid", False)  # directional
    add_edge("Warsaw", "Oslo", True)
    add_edge("Oslo", "Dubrovnik", True)
    add_edge("Oslo", "Reykjavik", True)
    add_edge("Riga", "Oslo", True)
    add_edge("Oslo", "Lyon", True)
    add_edge("Oslo", "London", True)
    add_edge("London", "Reykjavik", True)
    add_edge("Warsaw", "Madrid", True)
    add_edge("Madrid", "Lyon", True)
    add_edge("Dubrovnik", "Madrid", True)
    return adj

def compute_day_ranges(sequence, durations):
    # Overlap rule: start_next = end_current
    starts = {}
    ends = {}
    current_start = 1
    for i, city in enumerate(sequence):
        starts[city] = current_start
        ends[city] = current_start + durations[city] - 1
        current_start = ends[city] if i < len(sequence) - 1 else current_start
    return starts, ends

def meets_event_constraints(starts, ends, events):
    for ev in events:
        city = ev["city"]
        d1, d2 = ev["covers_days"]
        if not (starts[city] <= d1 and ends[city] >= d2):
            return False
    return True

def main():
    # Input variables (constraints)
    total_days = 18
    durations = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3,
    }
    events = [
        {"city": "Riga", "covers_days": (4, 5)},        # meet friend between day 4 and 5
        {"city": "Dubrovnik", "covers_days": (7, 8)},   # wedding between day 7 and 8
    ]
    cities = list(durations.keys())
    city_count = len(cities)
    sum_durations = sum(durations.values())
    required_transitions = sum_durations - total_days  # must equal number of flights used
    
    # Basic feasibility checks
    if city_count != 8:
        raise ValueError("There must be exactly 8 cities.")
    if required_transitions != city_count - 1:
        raise ValueError("Durations vs total days are inconsistent with single daily direct flights.")
    
    adj = build_adjacency()
    
    solution = None
    # Try all permutations and pick the first that satisfies adjacency and event constraints
    # Alphabetical order keeps search deterministic
    for perm in itertools.permutations(sorted(cities)):
        # Check all cities are unique (permutation guarantees)
        # Check direct flights between consecutive cities (directional where applicable)
        ok = True
        for i in range(len(perm) - 1):
            a, b = perm[i], perm[i + 1]
            if b not in adj.get(a, set()):
                ok = False
                break
        if not ok:
            continue
        
        # Compute day ranges with overlap rule
        starts, ends = compute_day_ranges(perm, durations)
        
        # Verify trip spans exactly total_days
        if ends[perm[-1]] - starts[perm[0]] + 1 != total_days:
            continue
        
        # Check event constraints (must be in city across the specified boundary)
        if not meets_event_constraints(starts, ends, events):
            continue
        
        solution = (perm, starts, ends)
        break
    
    if solution is None:
        print(json.dumps({"error": "No feasible itinerary found satisfying all constraints."}))
        return
    
    perm, starts, ends = solution
    
    itinerary = []
    for city in perm:
        itinerary.append({
            "day_range": f"Day {starts[city]}-{ends[city]}",
            "place": city
        })
    
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()