# Requires: z3-solver
# pip install z3-solver
from z3 import *
import json

# Cities and indices
cities = [
    "Frankfurt",   # 0
    "Salzburg",    # 1
    "Athens",      # 2
    "Reykjavik",   # 3
    "Bucharest",   # 4
    "Valencia",    # 5
    "Vienna",      # 6
    "Amsterdam",   # 7
    "Stockholm",   # 8
    "Riga"         # 9
]
idx = {name: i for i, name in enumerate(cities)}
n_cities = len(cities)
n_days = 29

# Build directed adjacency (allowed direct flights)
allowed_pairs = set()

def add_bidirectional(a, b):
    allowed_pairs.add((idx[a], idx[b]))
    allowed_pairs.add((idx[b], idx[a]))

def add_direct(a, b):
    allowed_pairs.add((idx[a], idx[b]))

# Staying in the same city (no flight) is always allowed
for i in range(n_cities):
    allowed_pairs.add((i, i))

# Flights list:
add_bidirectional("Valencia", "Frankfurt")
add_bidirectional("Vienna", "Bucharest")
add_direct("Valencia", "Athens")
add_bidirectional("Athens", "Bucharest")
add_bidirectional("Riga", "Frankfurt")
add_bidirectional("Stockholm", "Athens")
add_bidirectional("Amsterdam", "Bucharest")
add_direct("Athens", "Riga")
add_bidirectional("Amsterdam", "Frankfurt")
add_bidirectional("Stockholm", "Vienna")
add_bidirectional("Vienna", "Riga")
add_bidirectional("Amsterdam", "Reykjavik")
add_bidirectional("Reykjavik", "Frankfurt")
add_bidirectional("Stockholm", "Amsterdam")
add_bidirectional("Amsterdam", "Valencia")
add_bidirectional("Vienna", "Frankfurt")
add_bidirectional("Valencia", "Bucharest")
add_bidirectional("Bucharest", "Frankfurt")
add_bidirectional("Stockholm", "Frankfurt")
add_bidirectional("Valencia", "Vienna")
add_direct("Reykjavik", "Athens")
add_bidirectional("Frankfurt", "Salzburg")
add_bidirectional("Amsterdam", "Vienna")
add_bidirectional("Stockholm", "Reykjavik")
add_bidirectional("Amsterdam", "Riga")
add_bidirectional("Stockholm", "Riga")
add_bidirectional("Vienna", "Reykjavik")
add_bidirectional("Amsterdam", "Athens")
add_bidirectional("Athens", "Frankfurt")
add_bidirectional("Vienna", "Athens")
add_bidirectional("Riga", "Bucharest")

# Desired total days per city (with flight-day double counting rule)
target_days = {
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
targets = [target_days[name] for name in cities]

# Z3 variables
City = [Int(f"city_{d+1}") for d in range(n_days)]
Change = [Bool(f"change_{d+1}") for d in range(1, n_days)]  # for days 2..29 represented as indices 1..28 here

# Domain constraints
domain_constraints = [And(City[d] >= 0, City[d] < n_cities) for d in range(n_days)]

# Direct flight adjacency constraints between consecutive days
adj_constraints = []
for d in range(1, n_days):  # day index d corresponds to day d+1 in 1-based; previous is d
    # Change[d-1] is True iff City[d] != City[d-1]
    adj_constraints.append(Change[d-1] == (City[d] != City[d-1]))
    # Allowed transition
    allowed_disj = []
    for (a, b) in allowed_pairs:
        allowed_disj.append(And(City[d-1] == a, City[d] == b))
    adj_constraints.append(Or(*allowed_disj))

# present[c][d] means city 'c' is "present" on day d+1 (1-based), i.e.
# present if City[d]==c OR (d>0 and Change[d] and City[d-1]==c)
present = [[Bool(f"present_{c}_{d+1}") for d in range(n_days)] for c in range(n_cities)]
present_constraints = []
for c in range(n_cities):
    for d in range(n_days):
        if d == 0:
            present_constraints.append(present[c][d] == (City[d] == c))
        else:
            present_constraints.append(
                present[c][d] ==
                Or(City[d] == c, And(Change[d-1], City[d-1] == c))
            )

# Total days per city (sum of present booleans equals targets)
count_constraints = []
for c in range(n_cities):
    count_constraints.append(
        Sum([If(present[c][d], 1, 0) for d in range(n_days)]) == targets[c]
    )

# Number of change days equals total extra counts = sum(targets) - n_days
total_changes_needed = sum(targets) - n_days  # 38 - 29 = 9
change_count_constraint = (Sum([If(Change[d], 1, 0) for d in range(n_days - 1)]) == total_changes_needed)

# Event window constraints
# - Meet a friend in Stockholm between day 1 and day 3 (inclusive): present at least one of those days
stockholm = idx["Stockholm"]
event1 = Or(*[present[stockholm][d] for d in range(0, 3)])

# - Annual show in Valencia on day 5 and day 6: present on both days
valencia = idx["Valencia"]
event2 = And(present[valencia][4], present[valencia][5])  # indices 4->day5, 5->day6

# - Wedding in Vienna between day 6 and day 10: present at least one day in that window
vienna = idx["Vienna"]
event3 = Or(*[present[vienna][d] for d in range(5, 10)])

# - Workshop in Athens between day 14 and day 18: present at least one day in that window
athens = idx["Athens"]
event4 = Or(*[present[athens][d] for d in range(13, 18)])

# - Conference in Riga during day 18 to day 20 inclusive: present on all days 18, 19, 20
riga = idx["Riga"]
event5 = And(present[riga][17], present[riga][18], present[riga][19])  # 17->day18, 18->day19, 19->day20

# Build solver
s = Solver()
s.add(domain_constraints + adj_constraints + present_constraints + count_constraints + [change_count_constraint,
                                                                                        event1, event2, event3, event4, event5])

# Solve
if s.check() != sat:
    print(json.dumps({"error": "No solution found"}))
else:
    m = s.model()
    itinerary = []
    for d in range(n_days):
        c_idx = m.evaluate(City[d]).as_long()
        itinerary.append({"day": d + 1, "city": cities[c_idx]})
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))