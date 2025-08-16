from z3 import Solver, Int, And, sat
from itertools import permutations
import json

def minutes(h, m):
    return h * 60 + m

def fmt(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Travel times in minutes (asymmetric)
travel = {
    "Nob Hill": {
        "North Beach": 8,
        "Fisherman's Wharf": 11,
        "Bayview": 19
    },
    "North Beach": {
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Bayview": 22
    },
    "Fisherman's Wharf": {
        "Nob Hill": 11,
        "North Beach": 6,
        "Bayview": 26
    },
    "Bayview": {
        "Nob Hill": 20,
        "North Beach": 21,
        "Fisherman's Wharf": 25
    }
}

# People data
people = {
    "Helen": {
        "loc": "North Beach",
        "start": minutes(7, 0),
        "end": minutes(16, 45),
        "min_dur": 120
    },
    "Kimberly": {
        "loc": "Fisherman's Wharf",
        "start": minutes(16, 30),
        "end": minutes(21, 0),
        "min_dur": 45
    },
    "Patricia": {
        "loc": "Bayview",
        "start": minutes(18, 0),
        "end": minutes(21, 15),
        "min_dur": 120
    }
}

start_loc = "Nob Hill"
arrive_time = minutes(9, 0)

names = list(people.keys())

best = None  # (count, last_end_time, itinerary)

def solve_sequence(seq):
    s = Solver()
    n = len(seq)
    starts = [Int(f"start_{i}") for i in range(n)]
    ends = [Int(f"end_{i}") for i in range(n)]

    for i, name in enumerate(seq):
        p = people[name]
        s.add(starts[i] >= 0, ends[i] >= 0)
        s.add(starts[i] >= p["start"])
        s.add(ends[i] <= p["end"])
        s.add(ends[i] - starts[i] >= p["min_dur"])

    # Travel constraints
    if n >= 1:
        first_loc = people[seq[0]]["loc"]
        s.add(starts[0] >= arrive_time + travel[start_loc][first_loc])
    for i in range(1, n):
        prev_loc = people[seq[i-1]]["loc"]
        cur_loc = people[seq[i]]["loc"]
        s.add(starts[i] >= ends[i-1] + travel[prev_loc][cur_loc])

    if s.check() != sat:
        return None

    m = s.model()
    itinerary = []
    for i, name in enumerate(seq):
        st = m[starts[i]].as_long()
        en = m[ends[i]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": fmt(st),
            "end_time": fmt(en)
        })
    last_end = m[ends[-1]].as_long() if n > 0 else arrive_time
    return itinerary, last_end

# Try permutations of size 3 down to 1, choose the one that maximizes count,
# and among ties, choose the one with earliest final end time.
for size in range(3, 0, -1):
    best_for_size = None
    for seq in permutations(names, size):
        res = solve_sequence(seq)
        if res is None:
            continue
        itinerary, last_end = res
        if best_for_size is None or last_end < best_for_size[1]:
            best_for_size = (itinerary, last_end)
    if best_for_size is not None:
        best = (size, best_for_size[1], best_for_size[0])
        break

# Fallback if nothing found (shouldn't happen here)
output_itinerary = best[2] if best else []

# Print JSON result
print(json.dumps({"itinerary": output_itinerary}, ensure_ascii=False))