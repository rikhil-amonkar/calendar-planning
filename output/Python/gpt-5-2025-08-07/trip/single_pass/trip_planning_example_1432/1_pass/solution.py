import json

def parse_flights(raw_str):
    # Parse the raw flight connectivity text into a directed adjacency set
    edges = set()
    parts = [p.strip() for p in raw_str.strip().split(",")]
    for p in parts:
        p = p.strip().rstrip(".")
        if not p:
            continue
        if p.startswith("from "):
            # format: from A to B
            rest = p[len("from "):]
            if " to " not in rest:
                continue
            a, b = rest.split(" to ")
            a = a.strip().title()
            b = b.strip().title()
            edges.add((a, b))
        elif " and " in p:
            a, b = p.split(" and ")
            a = a.strip().title()
            b = b.strip().title()
            edges.add((a, b))
            edges.add((b, a))
        else:
            # Unexpected format; ignore
            pass
    return edges

# Inputs from the problem statement
total_days = 29

# Required stays (exact day counts)
durations = {
    "Frankfurt": 4,
    "Salzburg": 5,
    "Athens": 5,
    "Reykjavik": 5,
    "Bucharest": 3,
    "Valencia": 2,
    "Vienna": 5,
    "Amsterdam": 3,
    "Stockholm": 3,
    "Riga": 3,
}

# Event windows (inclusive day ranges to be present in that city)
event_windows = {
    "Stockholm": [(1, 3)],           # meet friend
    "Valencia": [(5, 6)],            # annual show
    "Vienna": [(6, 10)],             # wedding
    "Athens": [(14, 18)],            # workshop
    "Riga": [(18, 20)],              # conference
}

# Direct flights text (as provided)
flights_text = """
Valencia and Frankfurt, Vienna and Bucharest, from Valencia to Athens, Athens and Bucharest,
Riga and Frankfurt, Stockholm and Athens, Amsterdam and Bucharest, from Athens to Riga,
Amsterdam and Frankfurt, Stockholm and Vienna, Vienna and Riga, Amsterdam and Reykjavik,
Reykjavik and Frankfurt, Stockholm and Amsterdam, Amsterdam and Valencia, Vienna and Frankfurt,
Valencia and Bucharest, Bucharest and Frankfurt, Stockholm and Frankfurt, Valencia and Vienna,
from Reykjavik to Athens, Frankfurt and Salzburg, Amsterdam and Vienna, Stockholm and Reykjavik,
Amsterdam and Riga, Stockholm and Riga, Vienna and Reykjavik, Amsterdam and Athens,
Athens and Frankfurt, Vienna and Athens, Riga and Bucharest.
"""

edges = parse_flights(flights_text)

def has_direct(a, b):
    return (a, b) in edges

# Cities set
cities = list(durations.keys())

# We construct an order of the 10 cities (1..10) so that:
# - The block schedule with 1-day overlap between consecutive cities fits the event windows on exact days.
# - Every transition is a direct flight.
# Strategy:
# Fix positions forced by event windows and durations overlap math:
# Using overlap schedule, the start day of city k (1-indexed) equals:
#   start_1 = 1
#   start_k = start_{k-1} + duration_{k-1} - 1  (i.e., overlap one day)
# With durations, the start days of positions are:
# pos1=1
# pos2=3
# pos3=5
# pos4=6
# pos5=10
# pos6=14
# pos7=18
# pos8=20
# pos9=22
# pos10=25
# Event windows force:
# pos1 = Stockholm (days 1-3)
# pos3 = Valencia (days 5-6)
# pos4 = Vienna (days 6-10)
# pos6 = Athens (days 14-18)
# pos7 = Riga (days 18-20)
# Additionally, Salzburg must follow Frankfurt (only direct), so pos10=Salzburg => pos9 must be Frankfurt.
# Remaining cities to place into pos2, pos5, pos8, pos9 (but pos9 known Frankfurt): Amsterdam, Reykjavik, Bucharest.
# We'll solve the few remaining positions by backtracking with direct edge constraints.

positions = [None] * 11  # 1-based for clarity

# Fixed assignments
positions[1] = "Stockholm"
positions[3] = "Valencia"
positions[4] = "Vienna"
positions[6] = "Athens"
positions[7] = "Riga"
positions[10] = "Salzburg"

remaining = set(cities) - {positions[i] for i in range(1, 11) if positions[i]}

# Helper to check adjacency feasibility with known neighbors
def neighbors_ok(pos_idx, city, current_positions):
    left = current_positions[pos_idx - 1] if pos_idx - 1 >= 1 else None
    right = current_positions[pos_idx + 1] if pos_idx + 1 <= 10 else None
    if left is not None and not has_direct(left, city):
        return False
    if right is not None and not has_direct(city, right):
        return False
    return True

# We know pos9 must be Frankfurt because pos10 = Salzburg and only Frankfurt has direct to Salzburg
positions[9] = "Frankfurt"
remaining.discard("Frankfurt")

# Positions to solve (with some right/left neighbors known): pos2, pos5, pos8
to_fill = [2, 5, 8]

solutions = []

def backtrack(idx, rem, pos):
    if idx == len(to_fill):
        solutions.append(pos[:])
        return
    p = to_fill[idx]
    for city in list(rem):
        # Place city tentatively if neighbors ok
        pos[p] = city
        if neighbors_ok(p, city, pos):
            # Also enforce any future neighbor that is already fixed
            ok = True
            # Check neighbor to left if known
            if p - 1 >= 1 and pos[p - 1] is not None and not has_direct(pos[p - 1], city):
                ok = False
            # Check neighbor to right if known
            if p + 1 <= 10 and pos[p + 1] is not None and not has_direct(city, pos[p + 1]):
                ok = False
            if ok:
                rem2 = set(rem)
                rem2.remove(city)
                backtrack(idx + 1, rem2, pos)
        pos[p] = None

# Seed immediate neighbors for constraint checking
# Set neighbors explicitly for fixed positions to help pruning
# pos2 must connect from pos1=Stockholm and to pos3=Valencia
# pos5 must connect from pos4=Vienna and to pos6=Athens
# pos8 must connect from pos7=Riga and to pos9=Frankfurt

backtrack(0, remaining, positions[:])

if not solutions:
    raise RuntimeError("No valid city order found that satisfies direct-flight constraints and event windows.")
# Choose the first solution (should be unique)
order = solutions[0]
# Build ordered list for positions 1..10
city_order = [order[i] for i in range(1, 11)]

# Compute day ranges with 1-day overlap between consecutive cities
segments = []
start_day = 1
for i, city in enumerate(city_order):
    dur = durations[city]
    end_day = start_day + dur - 1
    segments.append((start_day, end_day, city))
    start_day = end_day  # overlap 1 day with next

# Validate total days end on 29
if segments[-1][1] != total_days:
    raise RuntimeError(f"Computed itinerary does not end on Day {total_days}, ends on Day {segments[-1][1]}")

# Validate event windows
for city, ranges in event_windows.items():
    seg = next((s for s in segments if s[2] == city), None)
    if not seg:
        raise RuntimeError(f"City {city} not in itinerary")
    s_day, e_day, _ = seg
    for (req_s, req_e) in ranges:
        if not (s_day <= req_s and e_day >= req_e):
            raise RuntimeError(f"Event window {city} Day {req_s}-{req_e} not covered by stay Day {s_day}-{e_day}")

# Validate all transitions are direct flights
for i in range(len(city_order) - 1):
    a = city_order[i]
    b = city_order[i + 1]
    if not has_direct(a, b):
        raise RuntimeError(f"No direct flight from {a} to {b}, but itinerary requires it.")

# Validate that durations match exactly when counting overlap as presence in both cities
# Build presence map per city per day
presence = {c: set() for c in cities}
# Mark presence for segments (with overlap)
for i, (s_day, e_day, city) in enumerate(segments):
    # City is present on [s_day, e_day]
    for d in range(s_day, e_day + 1):
        presence[city].add(d)
# Check exact durations
for c in cities:
    if len(presence[c]) != durations[c]:
        raise RuntimeError(f"City {c} presence days {len(presence[c])} != required {durations[c]}")

# Output itinerary in requested JSON format
itinerary = []
for s_day, e_day, city in segments:
    itinerary.append({
        "day_range": f"Day {s_day}-{e_day}",
        "place": city
    })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))