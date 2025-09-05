import json
import itertools

def build_adjacency():
    cities = [
        "Riga", "Manchester", "Bucharest", "Florence",
        "Vienna", "Istanbul", "Reykjavik", "Stuttgart"
    ]
    adj = {c: set() for c in cities}
    def add_edge(a, b, bidirectional=True):
        adj[a].add(b)
        if bidirectional:
            adj[b].add(a)
    # Direct flights as provided
    add_edge("Bucharest", "Vienna", True)
    add_edge("Reykjavik", "Vienna", True)
    add_edge("Manchester", "Vienna", True)
    add_edge("Manchester", "Riga", True)
    add_edge("Riga", "Vienna", True)
    add_edge("Istanbul", "Vienna", True)
    add_edge("Vienna", "Florence", True)
    add_edge("Stuttgart", "Vienna", True)
    add_edge("Riga", "Bucharest", True)
    add_edge("Istanbul", "Riga", True)
    add_edge("Stuttgart", "Istanbul", True)
    add_edge("Reykjavik", "Stuttgart", False)  # directed: from Reykjavik to Stuttgart
    add_edge("Istanbul", "Bucharest", True)
    add_edge("Manchester", "Istanbul", True)
    add_edge("Manchester", "Bucharest", True)
    add_edge("Stuttgart", "Manchester", True)
    return adj

def compute_schedule(order, durations, total_days):
    # Calculate start and end days with boundary overlap rule
    starts = {}
    ends = {}
    cumulative_before = 0
    for idx, city in enumerate(order):
        start = 1 + cumulative_before - idx
        end = start + durations[city] - 1
        starts[city] = start
        ends[city] = end
        cumulative_before += durations[city]
    # Validate timeline end
    if ends[order[-1]] != total_days or starts[order[0]] != 1:
        return None
    # Build itinerary list
    itinerary = []
    for city in order:
        itinerary.append({
            "day_range": f"Day {starts[city]}-{ends[city]}",
            "place": city
        })
    return itinerary, starts, ends

def find_itinerary(cities, durations, total_days, adjacency, event_windows):
    # Ensure total days align with overlap rule: sum(durations) - (n-1) == total_days
    n = len(cities)
    if sum(durations[c] for c in cities) - (n - 1) != total_days:
        return None

    for order in itertools.permutations(cities):
        # Check direct flights along the path
        valid_path = True
        for i in range(len(order) - 1):
            if order[i+1] not in adjacency.get(order[i], set()):
                valid_path = False
                break
        if not valid_path:
            continue

        result = compute_schedule(order, durations, total_days)
        if not result:
            continue
        itinerary, starts, ends = result

        # Check event constraints: exact days for Istanbul and Bucharest
        ist_win = event_windows.get("Istanbul")
        buch_win = event_windows.get("Bucharest")
        if ist_win and not (starts["Istanbul"] == ist_win[0] and ends["Istanbul"] == ist_win[1]):
            continue
        if buch_win and not (starts["Bucharest"] == buch_win[0] and ends["Bucharest"] == buch_win[1]):
            continue

        return itinerary

    return None

def main():
    # Input variables based on the constraints
    total_days = 23
    durations = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5
    }
    cities = list(durations.keys())
    adjacency = build_adjacency()
    # Event constraints: exact presence windows
    event_windows = {
        "Istanbul": (12, 13),
        "Bucharest": (16, 19)
    }

    itinerary = find_itinerary(cities, durations, total_days, adjacency, event_windows)
    if itinerary is None:
        output = {"error": "No feasible itinerary satisfying all constraints was found."}
    else:
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()