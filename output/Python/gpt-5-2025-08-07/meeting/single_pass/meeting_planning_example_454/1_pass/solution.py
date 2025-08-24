import json
from itertools import permutations

def to_minutes(h, m):
    return h * 60 + m

def parse_time_str(s):
    # expects 'H:MM' or 'HH:MM' 24h
    parts = s.strip().split(':')
    return to_minutes(int(parts[0]), int(parts[1]))

def fmt_minutes(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (meeting constraints)
start_location = "Presidio"
arrival_time_str = "9:00"

participants = [
    {
        "name": "Jessica",
        "location": "Golden Gate Park",
        "window_start": "13:45",
        "window_end": "15:00",
        "min_minutes": 30
    },
    {
        "name": "Ashley",
        "location": "Bayview",
        "window_start": "17:15",
        "window_end": "20:00",
        "min_minutes": 105
    },
    {
        "name": "Ronald",
        "location": "Chinatown",
        "window_start": "7:15",
        "window_end": "14:45",
        "min_minutes": 90
    },
    {
        "name": "William",
        "location": "North Beach",
        "window_start": "13:15",
        "window_end": "20:15",
        "min_minutes": 15
    },
    {
        "name": "Daniel",
        "location": "Mission District",
        "window_start": "7:00",
        "window_end": "11:15",
        "min_minutes": 105
    },
]

# Convert participant time strings to minutes
for p in participants:
    p["window_start_min"] = parse_time_str(p["window_start"])
    p["window_end_min"] = parse_time_str(p["window_end"])

start_time_min = parse_time_str(arrival_time_str)

# Travel times (in minutes), directed
travel = {
    "Presidio": {
        "Golden Gate Park": 12,
        "Bayview": 31,
        "Chinatown": 21,
        "North Beach": 18,
        "Mission District": 26,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Bayview": 23,
        "Chinatown": 23,
        "North Beach": 24,
        "Mission District": 17,
    },
    "Bayview": {
        "Presidio": 31,
        "Golden Gate Park": 22,
        "Chinatown": 18,
        "North Beach": 21,
        "Mission District": 13,
    },
    "Chinatown": {
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 22,
        "North Beach": 3,
        "Mission District": 18,
    },
    "North Beach": {
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 22,
        "Chinatown": 6,
        "Mission District": 18,
    },
    "Mission District": {
        "Presidio": 25,
        "Golden Gate Park": 17,
        "Bayview": 15,
        "Chinatown": 16,
        "North Beach": 17,
    },
}

def simulate_schedule(seq):
    itinerary = []
    cur_loc = start_location
    cur_time = start_time_min
    total_travel = 0
    total_wait = 0
    total_meet = 0

    for p in seq:
        t = travel[cur_loc][p["location"]]
        arrival = cur_time + t
        total_travel += t

        start_meet = max(arrival, p["window_start_min"])
        if start_meet > p["window_end_min"]:
            return None  # cannot meet at all

        wait_here = max(0, p["window_start_min"] - arrival)
        total_wait += wait_here

        end_meet = start_meet + p["min_minutes"]
        if end_meet > p["window_end_min"]:
            return None  # cannot fit minimum meeting

        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_minutes(start_meet),
            "end_time": fmt_minutes(end_meet),
        })
        total_meet += p["min_minutes"]
        cur_loc = p["location"]
        cur_time = end_meet

    return {
        "itinerary": itinerary,
        "final_end": cur_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "total_meet": total_meet,
        "met_count": len(seq),
    }

def find_optimal_schedule(participants):
    n = len(participants)
    best = None

    # Search schedules by meeting as many friends as possible first
    for k in range(n, 0, -1):
        # For tie-breaking within same k, we collect best candidate
        best_k = None
        for seq in permutations(participants, k):
            res = simulate_schedule(seq)
            if res is None:
                continue
            # Tie-breaking: prioritize earliest final finish, then minimal total wait, then minimal travel
            if best_k is None:
                best_k = (seq, res)
            else:
                _, br = best_k
                if (res["final_end"] < br["final_end"] or
                    (res["final_end"] == br["final_end"] and res["total_wait"] < br["total_wait"]) or
                    (res["final_end"] == br["final_end"] and res["total_wait"] == br["total_wait"] and res["total_travel"] < br["total_travel"])):
                    best_k = (seq, res)
        if best_k is not None:
            best = best_k
            break

    return best

best_seq, best_res = find_optimal_schedule(participants)

# Prepare JSON output
output = {
    "itinerary": best_res["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))