"""SOLUTION:"""
import json

def minutes(h, m):
    return h*60 + m

def time_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
travel = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25,
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27,
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20,
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21,
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22,
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16,
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16,
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6,
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21,
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 17,
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16,
    },
}

start_location = "Embarcadero"
start_time = minutes(9, 0)

friends = [
    {"person": "Stephanie", "location": "Fisherman's Wharf", "start": minutes(15, 30), "end": minutes(22, 0), "min_duration": 30},
    {"person": "Lisa", "location": "Financial District", "start": minutes(10, 45), "end": minutes(17, 15), "min_duration": 15},
    {"person": "Melissa", "location": "Russian Hill", "start": minutes(17, 0), "end": minutes(21, 45), "min_duration": 120},
    {"person": "Betty", "location": "Marina District", "start": minutes(10, 45), "end": minutes(14, 15), "min_duration": 60},
    {"person": "Sarah", "location": "Richmond District", "start": minutes(16, 15), "end": minutes(19, 30), "min_duration": 105},
    {"person": "Daniel", "location": "Pacific Heights", "start": minutes(18, 30), "end": minutes(21, 45), "min_duration": 60},
    {"person": "Joshua", "location": "Haight-Ashbury", "start": minutes(9, 0), "end": minutes(15, 30), "min_duration": 15},
    {"person": "Joseph", "location": "Presidio", "start": minutes(7, 0), "end": minutes(13, 0), "min_duration": 45},
    {"person": "Andrew", "location": "Nob Hill", "start": minutes(19, 45), "end": minutes(22, 0), "min_duration": 105},
    {"person": "John", "location": "The Castro", "start": minutes(13, 15), "end": minutes(19, 45), "min_duration": 45},
]

n = len(friends)

# DP: state -> { 'finish': t, 'prev_mask': pm, 'prev_j': j, 'start_time': ts }
# Use a list of dicts for masks, and for each mask, a list of states for ending at j
INF = 10**9
dp_finish = [[INF]*n for _ in range(1<<n)]
dp_prev_mask = [[None]*n for _ in range(1<<n)]
dp_prev_j = [[None]*n for _ in range(1<<n)]
dp_meet_start = [[None]*n for _ in range(1<<n)]

# Initialize singletons
for j in range(n):
    loc = friends[j]["location"]
    wstart = friends[j]["start"]
    wend = friends[j]["end"]
    dur = friends[j]["min_duration"]
    # Travel from start
    t_travel = travel[start_location][loc]
    arrive = start_time + t_travel
    meet_start = max(arrive, wstart)
    meet_end = meet_start + dur
    if meet_end <= wend:
        mask = 1 << j
        dp_finish[mask][j] = meet_end
        dp_prev_mask[mask][j] = 0
        dp_prev_j[mask][j] = -1
        dp_meet_start[mask][j] = meet_start

# Transitions
for mask in range(1<<n):
    for j in range(n):
        if not (mask & (1<<j)):
            continue
        if dp_finish[mask][j] == INF:
            continue
        time_at_j = dp_finish[mask][j]
        loc_j = friends[j]["location"]
        # Try to go to k not yet visited
        for k in range(n):
            if mask & (1<<k):
                continue
            loc_k = friends[k]["location"]
            wstart = friends[k]["start"]
            wend = friends[k]["end"]
            dur = friends[k]["min_duration"]
            # Travel j -> k
            t_travel = travel[loc_j][loc_k]
            arrive = time_at_j + t_travel
            meet_start = max(arrive, wstart)
            meet_end = meet_start + dur
            if meet_end <= wend:
                newmask = mask | (1<<k)
                if meet_end < dp_finish[newmask][k]:
                    dp_finish[newmask][k] = meet_end
                    dp_prev_mask[newmask][k] = mask
                    dp_prev_j[newmask][k] = j
                    dp_meet_start[newmask][k] = meet_start

# Select best mask (max count), tie-break: earliest finish time
best_mask = 0
best_j = None
best_finish = INF
best_count = -1
for mask in range(1<<n):
    count = bin(mask).count("1")
    if count < best_count:
        continue
    for j in range(n):
        if dp_finish[mask][j] == INF:
            continue
        if count > best_count or (count == best_count and dp_finish[mask][j] < best_finish):
            best_count = count
            best_finish = dp_finish[mask][j]
            best_mask = mask
            best_j = j

# Reconstruct path
order = []
mask = best_mask
j = best_j
while j is not None and j != -1 and mask:
    meet_end = dp_finish[mask][j]
    meet_start = dp_meet_start[mask][j]
    order.append((j, meet_start, meet_end))
    pm = dp_prev_mask[mask][j]
    pj = dp_prev_j[mask][j]
    mask, j = pm, pj

order.reverse()

# Build itinerary JSON
itinerary = []
for (idx, st, en) in order:
    entry = {
        "action": "meet",
        "location": friends[idx]["location"],
        "person": friends[idx]["person"],
        "start_time": time_str(st),
        "end_time": time_str(en),
    }
    itinerary.append(entry)

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))