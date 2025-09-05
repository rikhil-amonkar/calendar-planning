import json
from collections import defaultdict

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes), directed
travel = defaultdict(dict)
data = [
    ("Union Square", "Presidio", 24),
    ("Union Square", "Alamo Square", 15),
    ("Union Square", "Marina District", 18),
    ("Union Square", "Financial District", 9),
    ("Union Square", "Nob Hill", 9),
    ("Union Square", "Sunset District", 27),
    ("Union Square", "Chinatown", 7),
    ("Union Square", "Russian Hill", 13),
    ("Union Square", "North Beach", 10),
    ("Union Square", "Haight-Ashbury", 18),

    ("Presidio", "Union Square", 22),
    ("Presidio", "Alamo Square", 19),
    ("Presidio", "Marina District", 11),
    ("Presidio", "Financial District", 23),
    ("Presidio", "Nob Hill", 18),
    ("Presidio", "Sunset District", 15),
    ("Presidio", "Chinatown", 21),
    ("Presidio", "Russian Hill", 14),
    ("Presidio", "North Beach", 18),
    ("Presidio", "Haight-Ashbury", 15),

    ("Alamo Square", "Union Square", 14),
    ("Alamo Square", "Presidio", 17),
    ("Alamo Square", "Marina District", 15),
    ("Alamo Square", "Financial District", 17),
    ("Alamo Square", "Nob Hill", 11),
    ("Alamo Square", "Sunset District", 16),
    ("Alamo Square", "Chinatown", 15),
    ("Alamo Square", "Russian Hill", 13),
    ("Alamo Square", "North Beach", 15),
    ("Alamo Square", "Haight-Ashbury", 5),

    ("Marina District", "Union Square", 16),
    ("Marina District", "Presidio", 10),
    ("Marina District", "Alamo Square", 15),
    ("Marina District", "Financial District", 17),
    ("Marina District", "Nob Hill", 12),
    ("Marina District", "Sunset District", 19),
    ("Marina District", "Chinatown", 15),
    ("Marina District", "Russian Hill", 8),
    ("Marina District", "North Beach", 11),
    ("Marina District", "Haight-Ashbury", 16),

    ("Financial District", "Union Square", 9),
    ("Financial District", "Presidio", 22),
    ("Financial District", "Alamo Square", 17),
    ("Financial District", "Marina District", 15),
    ("Financial District", "Nob Hill", 8),
    ("Financial District", "Sunset District", 30),
    ("Financial District", "Chinatown", 5),
    ("Financial District", "Russian Hill", 11),
    ("Financial District", "North Beach", 7),
    ("Financial District", "Haight-Ashbury", 19),

    ("Nob Hill", "Union Square", 7),
    ("Nob Hill", "Presidio", 17),
    ("Nob Hill", "Alamo Square", 11),
    ("Nob Hill", "Marina District", 11),
    ("Nob Hill", "Financial District", 9),
    ("Nob Hill", "Sunset District", 24),
    ("Nob Hill", "Chinatown", 6),
    ("Nob Hill", "Russian Hill", 5),
    ("Nob Hill", "North Beach", 8),
    ("Nob Hill", "Haight-Ashbury", 13),

    ("Sunset District", "Union Square", 30),
    ("Sunset District", "Presidio", 16),
    ("Sunset District", "Alamo Square", 17),
    ("Sunset District", "Marina District", 21),
    ("Sunset District", "Financial District", 30),
    ("Sunset District", "Nob Hill", 27),
    ("Sunset District", "Chinatown", 30),
    ("Sunset District", "Russian Hill", 24),
    ("Sunset District", "North Beach", 28),
    ("Sunset District", "Haight-Ashbury", 15),

    ("Chinatown", "Union Square", 7),
    ("Chinatown", "Presidio", 19),
    ("Chinatown", "Alamo Square", 17),
    ("Chinatown", "Marina District", 12),
    ("Chinatown", "Financial District", 5),
    ("Chinatown", "Nob Hill", 9),
    ("Chinatown", "Sunset District", 29),
    ("Chinatown", "Russian Hill", 7),
    ("Chinatown", "North Beach", 3),
    ("Chinatown", "Haight-Ashbury", 19),

    ("Russian Hill", "Union Square", 10),
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "Alamo Square", 15),
    ("Russian Hill", "Marina District", 7),
    ("Russian Hill", "Financial District", 11),
    ("Russian Hill", "Nob Hill", 5),
    ("Russian Hill", "Sunset District", 23),
    ("Russian Hill", "Chinatown", 9),
    ("Russian Hill", "North Beach", 5),
    ("Russian Hill", "Haight-Ashbury", 17),

    ("North Beach", "Union Square", 7),
    ("North Beach", "Presidio", 17),
    ("North Beach", "Alamo Square", 16),
    ("North Beach", "Marina District", 9),
    ("North Beach", "Financial District", 8),
    ("North Beach", "Nob Hill", 7),
    ("North Beach", "Sunset District", 27),
    ("North Beach", "Chinatown", 6),
    ("North Beach", "Russian Hill", 4),
    ("North Beach", "Haight-Ashbury", 18),

    ("Haight-Ashbury", "Union Square", 19),
    ("Haight-Ashbury", "Presidio", 15),
    ("Haight-Ashbury", "Alamo Square", 5),
    ("Haight-Ashbury", "Marina District", 17),
    ("Haight-Ashbury", "Financial District", 21),
    ("Haight-Ashbury", "Nob Hill", 15),
    ("Haight-Ashbury", "Sunset District", 15),
    ("Haight-Ashbury", "Chinatown", 19),
    ("Haight-Ashbury", "Russian Hill", 17),
    ("Haight-Ashbury", "North Beach", 19),
]
for a, b, t in data:
    travel[a][b] = t

# Start location/time
start_location = "Union Square"
start_time = minutes(9, 0)  # 9:00

# Meeting constraints
meetings = [
    {"person": "Kimberly", "location": "Presidio", "start": minutes(15, 30), "end": minutes(16, 0), "duration": 15},
    {"person": "Elizabeth", "location": "Alamo Square", "start": minutes(19, 15), "end": minutes(20, 15), "duration": 15},
    {"person": "Joshua", "location": "Marina District", "start": minutes(10, 30), "end": minutes(14, 15), "duration": 45},
    {"person": "Sandra", "location": "Financial District", "start": minutes(19, 30), "end": minutes(20, 15), "duration": 45},
    {"person": "Kenneth", "location": "Nob Hill", "start": minutes(12, 45), "end": minutes(21, 45), "duration": 30},
    {"person": "Betty", "location": "Sunset District", "start": minutes(14, 0), "end": minutes(19, 0), "duration": 60},
    {"person": "Deborah", "location": "Chinatown", "start": minutes(17, 15), "end": minutes(20, 30), "duration": 15},
    {"person": "Barbara", "location": "Russian Hill", "start": minutes(17, 30), "end": minutes(21, 15), "duration": 120},
    {"person": "Steven", "location": "North Beach", "start": minutes(17, 45), "end": minutes(20, 45), "duration": 90},
    {"person": "Daniel", "location": "Haight-Ashbury", "start": minutes(18, 30), "end": minutes(18, 45), "duration": 15},
]
# Keep a fixed order (index matters for DP)
# Reorder to more natural but not necessary
# We'll keep as listed above.

N = len(meetings)

class Node:
    def __init__(self, end_time, prev_key, start_time, total_travel, total_wait):
        self.end_time = end_time
        self.prev_key = prev_key
        self.start_time = start_time
        self.total_travel = total_travel
        self.total_wait = total_wait

def bit_count(x):
    return bin(x).count("1")

# DP: key = (mask, last_index), last_index in {-1..N-1}; use -1 for start
dp = {}
start_key = (0, -1)
dp[start_key] = Node(end_time=start_time, prev_key=None, start_time=None, total_travel=0, total_wait=0)

# Iterate over increasing mask sizes
for mask in range(1 << N):
    for last in range(-1, N):
        key = (mask, last)
        if key not in dp:
            continue
        node = dp[key]
        prev_loc = start_location if last == -1 else meetings[last]["location"]
        for i in range(N):
            if mask & (1 << i):
                continue
            m = meetings[i]
            # Travel time from prev_loc to m['location']
            t_travel = travel[prev_loc].get(m["location"])
            if t_travel is None:
                continue
            arrival = node.end_time + t_travel
            start_meet = max(arrival, m["start"])
            end_meet = start_meet + m["duration"]
            if end_meet <= m["end"]:
                new_mask = mask | (1 << i)
                new_key = (new_mask, i)
                wait = max(0, start_meet - arrival)
                total_travel = node.total_travel + t_travel
                total_wait = node.total_wait + wait
                new_node = Node(end_time=end_meet, prev_key=key, start_time=start_meet,
                                total_travel=total_travel, total_wait=total_wait)
                if new_key not in dp:
                    dp[new_key] = new_node
                else:
                    existing = dp[new_key]
                    # Prefer earlier end time, then less total wait, then less travel
                    if (new_node.end_time < existing.end_time or
                        (new_node.end_time == existing.end_time and new_node.total_wait < existing.total_wait) or
                        (new_node.end_time == existing.end_time and new_node.total_wait == existing.total_wait and new_node.total_travel < existing.total_travel)):
                        dp[new_key] = new_node

# Choose best solution by max number of meetings; tie-breaker earliest end, then less wait, then less travel
best_key = None
best_crit = None  # (-count, end_time, wait, travel) but we want max count so store negative?
for key, node in dp.items():
    mask, last = key
    if mask == 0:
        continue
    count = bit_count(mask)
    crit = (-count, node.end_time, node.total_wait, node.total_travel)
    if best_key is None or crit < best_crit:
        best_key = key
        best_crit = crit

# Reconstruct itinerary
itinerary = []
if best_key is not None:
    key = best_key
    while key is not None and key != start_key:
        mask, last = key
        node = dp[key]
        meet = meetings[last]
        itinerary.append({
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": minutes_to_str(node.start_time),
            "end_time": minutes_to_str(node.end_time)
        })
        key = node.prev_key
    itinerary.reverse()

output = {"itinerary": itinerary}

print("SOLUTION:")
print(json.dumps(output, ensure_ascii=False, indent=2))