import itertools
import json

# Input variables
total_days = 10
cities = ["Mykonos", "Vienna", "Venice"]
city_days_required = {
    "Venice": 6,
    "Mykonos": 2,
    "Vienna": 4,
}
# Mandatory presence intervals (inclusive) per city
mandatory_city_intervals = {
    "Venice": (5, 10)  # must be in Venice on days 5 through 10 inclusive
}
# Direct flights (undirected)
direct_flights = [
    ("Mykonos", "Vienna"),
    ("Vienna", "Venice"),
]

# Build adjacency for direct flights
adj = {}
for a, b in direct_flights:
    adj.setdefault(a, set()).add(b)
    adj.setdefault(b, set()).add(a)

# Helper: check if an ordering of cities is a valid path using only direct flights
def is_valid_path(order):
    for i in range(len(order) - 1):
        if order[i+1] not in adj.get(order[i], set()):
            return False
    return True

# Helper: compute day ranges for a 3-city path, honoring overlaps on flight days
def compute_day_ranges(order):
    # Let the day ranges be:
    # City1: [1, d12]
    # City2: [d12, d23]
    # City3: [d23, total_days]
    d1 = city_days_required[order[0]]
    d2 = city_days_required[order[1]]
    d3 = city_days_required[order[2]]

    # The overlaps imply:
    # d12 = d1
    # d23 = total_days - d3 + 1
    d12 = d1
    d23 = total_days - d3 + 1

    # Durations check for middle city:
    calc_d2 = d23 - d12 + 1
    if calc_d2 != d2:
        return None

    # Ensure valid chronological ordering
    if not (1 <= d12 <= d23 <= total_days):
        return None

    ranges = {
        order[0]: (1, d12),
        order[1]: (d12, d23),
        order[2]: (d23, total_days),
    }

    # Check mandatory intervals are fully covered by the assigned city ranges
    for city, (start_req, end_req) in mandatory_city_intervals.items():
        if city not in ranges:
            return None
        start_city, end_city = ranges[city]
        if not (start_city <= start_req and end_city >= end_req):
            return None

    # Confirm exact day counts
    for city in order:
        s, e = ranges[city]
        if e - s + 1 != city_days_required[city]:
            return None

    # Return as ordered list
    return [(order[0], ranges[order[0]]),
            (order[1], ranges[order[1]]),
            (order[2], ranges[order[2]])]

# Validate feasibility via total days sum rule: sum(city_days) must equal total_days + number_of_flights
if sum(city_days_required[c] for c in cities) != total_days + (len(cities) - 1):
    result = {"itinerary": []}
else:
    candidates = []
    for order in itertools.permutations(cities):
        if not is_valid_path(order):
            continue
        plan = compute_day_ranges(order)
        if plan:
            candidates.append(plan)

    # Choose an optimal plan: prefer the one whose Venice start aligns best with its mandatory interval start
    def score(plan):
        ven_range = next(r for c, r in plan if c == "Venice")
        ven_start = ven_range[0]
        mandatory_start = mandatory_city_intervals["Venice"][0]
        # Secondary tie-breaker: earlier cumulative flight days
        flight_days_sum = plan[0][1][1] + plan[1][1][1]
        return (abs(ven_start - mandatory_start), flight_days_sum)

    if not candidates:
        result = {"itinerary": []}
    else:
        best_plan = min(candidates, key=score)
        itinerary = [{"day_range": f"Day {s}-{e}", "place": city} for city, (s, e) in best_plan]
        result = {"itinerary": itinerary}

print(json.dumps(result, ensure_ascii=False))