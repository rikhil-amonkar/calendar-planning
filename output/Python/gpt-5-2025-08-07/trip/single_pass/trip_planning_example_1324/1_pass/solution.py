import json
import itertools

def main():
    # Input variables (constraints)
    total_days = 26
    cities = [
        "Lyon", "Venice", "Copenhagen", "Barcelona",
        "Reykjavik", "Athens", "Dubrovnik", "Munich", "Tallinn"
    ]
    durations = {
        "Venice": 4,
        "Barcelona": 3,
        "Copenhagen": 4,
        "Lyon": 4,
        "Reykjavik": 4,
        "Dubrovnik": 5,
        "Athens": 2,
        "Tallinn": 5,
        "Munich": 3
    }
    # Windows: must overlap within these inclusive day ranges
    windows = {
        "Barcelona": (10, 12),
        "Copenhagen": (7, 10),
        "Dubrovnik": (16, 20),
    }

    # Build adjacency (direct flights). "A and B" => bidirectional; "from X to Y" => X->Y only
    adj = {c: set() for c in cities}
    def add_bi(a, b):
        adj[a].add(b)
        adj[b].add(a)
    def add_dir(a, b):
        adj[a].add(b)

    add_bi("Copenhagen", "Athens")
    add_bi("Copenhagen", "Dubrovnik")
    add_bi("Munich", "Tallinn")
    add_bi("Copenhagen", "Munich")
    add_bi("Venice", "Munich")
    add_dir("Reykjavik", "Athens")
    add_bi("Athens", "Dubrovnik")
    add_bi("Venice", "Athens")
    add_bi("Lyon", "Barcelona")
    add_bi("Copenhagen", "Reykjavik")
    add_bi("Reykjavik", "Munich")
    add_bi("Athens", "Munich")
    add_bi("Lyon", "Munich")
    add_bi("Barcelona", "Reykjavik")
    add_bi("Venice", "Copenhagen")
    add_bi("Barcelona", "Dubrovnik")
    add_bi("Lyon", "Venice")
    add_bi("Dubrovnik", "Munich")
    add_bi("Barcelona", "Athens")
    add_bi("Copenhagen", "Barcelona")
    add_bi("Venice", "Barcelona")
    add_bi("Barcelona", "Munich")
    add_bi("Barcelona", "Tallinn")
    add_bi("Copenhagen", "Tallinn")

    # Pre-check: total city-days sum minus overlaps equals total_days
    sum_days = sum(durations[c] for c in cities)
    required_flights = len(cities) - 1
    assert sum_days - required_flights == total_days, "Durations/overlaps mismatch with total days"

    def compute_schedule(order):
        start = {}
        end = {}
        # Start day for first city
        start[order[0]] = 1
        end[order[0]] = start[order[0]] + durations[order[0]] - 1
        for i in range(1, len(order)):
            prev = order[i-1]
            curr = order[i]
            # Overlap travel day: next city starts on previous city's last day
            start[curr] = start[prev] + durations[prev] - 1
            end[curr] = start[curr] + durations[curr] - 1
        return start, end

    def windows_okay(start, end):
        for city, (lo, hi) in windows.items():
            if not (start[city] <= hi and end[city] >= lo):
                return False
        return True

    def adjacency_okay(order):
        for i in range(len(order) - 1):
            a, b = order[i], order[i+1]
            if b not in adj[a]:
                return False
        return True

    solution = None
    for perm in itertools.permutations(cities):
        # Quick adjacency check (cheap fail)
        if not adjacency_okay(perm):
            continue
        start, end = compute_schedule(perm)
        # Ensure trip aligns exactly with total_days
        if end[perm[-1]] != total_days:
            continue
        if not windows_okay(start, end):
            continue
        solution = (perm, start, end)
        break

    if solution is None:
        # No solution found; output empty itinerary
        itinerary = []
    else:
        order, start, end = solution
        itinerary = [{"day_range": f"Day {start[c]}-{end[c]}", "place": c} for c in order]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()