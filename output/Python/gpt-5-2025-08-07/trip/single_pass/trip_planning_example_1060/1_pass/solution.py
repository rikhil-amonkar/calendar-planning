import itertools
import json

def build_edges():
    # Directed edges set
    edges = set()
    # Geneva and Istanbul (bidirectional)
    edges.add(("Geneva", "Istanbul"))
    edges.add(("Istanbul", "Geneva"))
    # Reykjavik and Munich (bidirectional)
    edges.add(("Reykjavik", "Munich"))
    edges.add(("Munich", "Reykjavik"))
    # Stuttgart and Valencia (bidirectional)
    edges.add(("Stuttgart", "Valencia"))
    edges.add(("Valencia", "Stuttgart"))
    # from Reykjavik to Stuttgart (directed)
    edges.add(("Reykjavik", "Stuttgart"))
    # Stuttgart and Istanbul (bidirectional)
    edges.add(("Stuttgart", "Istanbul"))
    edges.add(("Istanbul", "Stuttgart"))
    # Munich and Geneva (bidirectional)
    edges.add(("Munich", "Geneva"))
    edges.add(("Geneva", "Munich"))
    # Istanbul and Vilnius (bidirectional)
    edges.add(("Istanbul", "Vilnius"))
    edges.add(("Vilnius", "Istanbul"))
    # Valencia and Seville (bidirectional)
    edges.add(("Valencia", "Seville"))
    edges.add(("Seville", "Valencia"))
    # Valencia and Istanbul (bidirectional)
    edges.add(("Valencia", "Istanbul"))
    edges.add(("Istanbul", "Valencia"))
    # from Vilnius to Munich (directed)
    edges.add(("Vilnius", "Munich"))
    # Seville and Munich (bidirectional)
    edges.add(("Seville", "Munich"))
    edges.add(("Munich", "Seville"))
    # Munich and Istanbul (bidirectional)
    edges.add(("Munich", "Istanbul"))
    edges.add(("Istanbul", "Munich"))
    # Valencia and Geneva (bidirectional)
    edges.add(("Valencia", "Geneva"))
    edges.add(("Geneva", "Valencia"))
    # Valencia and Munich (bidirectional)
    edges.add(("Valencia", "Munich"))
    edges.add(("Munich", "Valencia"))
    return edges

def compute_schedule(order, durations, total_days, edges):
    # Overlap model:
    # - start of first city is day 1
    # - start of next city equals end of previous city (travel day counts for both)
    # - end of city = start + duration - 1
    schedule = {}
    start_day = 1
    prev_end = None
    for i, city in enumerate(order):
        if i == 0:
            start = start_day
        else:
            start = prev_end  # Overlap on transition day
            # flight must exist from previous city to current city
            if (order[i - 1], city) not in edges:
                return None
        end = start + durations[city] - 1
        schedule[city] = (start, end)
        prev_end = end
    # total days must end on 'total_days'
    if prev_end != total_days:
        return None
    return schedule

def satisfies_anchors(schedule, anchors):
    # Check that required days fall within each city's scheduled interval
    for city, days in anchors.items():
        if city not in schedule:
            return False
        s, e = schedule[city]
        for d in days:
            if not (s <= d <= e):
                return False
    return True

def main():
    # Input variables (constraints)
    total_days = 25
    cities = ["Stuttgart", "Istanbul", "Vilnius", "Seville", "Geneva", "Valencia", "Munich", "Reykjavik"]
    durations = {
        "Stuttgart": 4,   # must include day 4 and day 7
        "Istanbul": 4,    # must include days 19-22
        "Vilnius": 4,
        "Seville": 3,
        "Geneva": 5,
        "Valencia": 5,
        "Munich": 3,      # must include days 13-15
        "Reykjavik": 4    # must include days 1-4
    }
    anchors = {
        "Reykjavik": {1, 2, 3, 4},       # workshop days 1-4
        "Stuttgart": {4, 7},             # conference on days 4 and 7
        "Munich": {13, 14, 15},          # annual show days 13-15
        "Istanbul": {19, 20, 21, 22}     # relatives days 19-22
    }
    edges = build_edges()

    # We must visit all 8 cities exactly once. We model overlapped transitions.
    # Reykjavik must start on day 1 (to cover days 1-4 with duration 4), so fix it as first.
    first_city = "Reykjavik"
    remaining = [c for c in cities if c != first_city]

    best_schedule = None
    best_order = None

    # Search over permutations with Reykjavik fixed first
    for perm in itertools.permutations(remaining):
        order = (first_city,) + perm
        schedule = compute_schedule(order, durations, total_days, edges)
        if schedule is None:
            continue
        if not satisfies_anchors(schedule, anchors):
            continue
        # Feasible plan found; since all durations are fixed, first feasible is optimal
        best_schedule = schedule
        best_order = order
        break

    if best_schedule is None:
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    # Build itinerary list sorted by start day
    itinerary = []
    # sort by start day
    order_sorted = sorted(best_schedule.items(), key=lambda x: x[1][0])
    for city, (s, e) in order_sorted:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()