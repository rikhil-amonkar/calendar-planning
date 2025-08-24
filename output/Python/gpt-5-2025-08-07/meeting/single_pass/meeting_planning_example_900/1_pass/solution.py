import json
from dataclasses import dataclass
from typing import Dict, List, Tuple

@dataclass
class Friend:
    name: str
    location: str
    start: int       # minutes since midnight
    end: int         # minutes since midnight
    min_duration: int  # minutes

def to_minutes(h: int, m: int) -> int:
    return h * 60 + m

def fmt_time(mins: int) -> str:
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Build travel times (minutes)
# Neighborhoods: Richmond District, The Castro, Nob Hill, Marina District, Pacific Heights,
# Haight-Ashbury, Mission District, Chinatown, Russian Hill, Alamo Square, Bayview
travel: Dict[str, Dict[str, int]] = {
    "Richmond District": {
        "The Castro": 16, "Nob Hill": 17, "Marina District": 9, "Pacific Heights": 10,
        "Haight-Ashbury": 10, "Mission District": 20, "Chinatown": 20, "Russian Hill": 13,
        "Alamo Square": 13, "Bayview": 27
    },
    "The Castro": {
        "Richmond District": 16, "Nob Hill": 16, "Marina District": 21, "Pacific Heights": 16,
        "Haight-Ashbury": 6, "Mission District": 7, "Chinatown": 22, "Russian Hill": 18,
        "Alamo Square": 8, "Bayview": 19
    },
    "Nob Hill": {
        "Richmond District": 14, "The Castro": 17, "Marina District": 11, "Pacific Heights": 8,
        "Haight-Ashbury": 13, "Mission District": 13, "Chinatown": 6, "Russian Hill": 5,
        "Alamo Square": 11, "Bayview": 19
    },
    "Marina District": {
        "Richmond District": 11, "The Castro": 22, "Nob Hill": 12, "Pacific Heights": 7,
        "Haight-Ashbury": 16, "Mission District": 20, "Chinatown": 15, "Russian Hill": 8,
        "Alamo Square": 15, "Bayview": 27
    },
    "Pacific Heights": {
        "Richmond District": 12, "The Castro": 16, "Nob Hill": 8, "Marina District": 6,
        "Haight-Ashbury": 12, "Mission District": 15, "Chinatown": 11, "Russian Hill": 7,
        "Alamo Square": 10, "Bayview": 22
    },
    "Haight-Ashbury": {
        "Richmond District": 10, "The Castro": 6, "Nob Hill": 15, "Marina District": 17,
        "Pacific Heights": 12, "Mission District": 11, "Chinatown": 19, "Russian Hill": 17,
        "Alamo Square": 5, "Bayview": 18
    },
    "Mission District": {
        "Richmond District": 20, "The Castro": 7, "Nob Hill": 12, "Marina District": 19,
        "Pacific Heights": 16, "Haight-Ashbury": 12, "Chinatown": 16, "Russian Hill": 15,
        "Alamo Square": 11, "Bayview": 14
    },
    "Chinatown": {
        "Richmond District": 20, "The Castro": 22, "Nob Hill": 9, "Marina District": 12,
        "Pacific Heights": 10, "Haight-Ashbury": 19, "Mission District": 17, "Russian Hill": 7,
        "Alamo Square": 17, "Bayview": 20
    },
    "Russian Hill": {
        "Richmond District": 14, "The Castro": 21, "Nob Hill": 5, "Marina District": 7,
        "Pacific Heights": 7, "Haight-Ashbury": 17, "Mission District": 16, "Chinatown": 9,
        "Alamo Square": 15, "Bayview": 23
    },
    "Alamo Square": {
        "Richmond District": 11, "The Castro": 8, "Nob Hill": 11, "Marina District": 15,
        "Pacific Heights": 10, "Haight-Ashbury": 5, "Mission District": 10, "Chinatown": 15,
        "Russian Hill": 13, "Bayview": 16
    },
    "Bayview": {
        "Richmond District": 25, "The Castro": 19, "Nob Hill": 20, "Marina District": 27,
        "Pacific Heights": 23, "Haight-Ashbury": 19, "Mission District": 13, "Chinatown": 19,
        "Russian Hill": 23, "Alamo Square": 16
    }
}

# Constraints (times in minutes since midnight)
friends: List[Friend] = [
    Friend("Matthew",   "The Castro",       to_minutes(16,30), to_minutes(20,0),  45),
    Friend("Rebecca",   "Nob Hill",         to_minutes(15,15), to_minutes(19,15), 105),
    Friend("Brian",     "Marina District",  to_minutes(14,15), to_minutes(22,0),  30),
    Friend("Emily",     "Pacific Heights",  to_minutes(11,15), to_minutes(19,45), 15),
    Friend("Karen",     "Haight-Ashbury",   to_minutes(11,45), to_minutes(17,30), 30),
    Friend("Stephanie", "Mission District", to_minutes(13,0),  to_minutes(15,45), 75),
    Friend("James",     "Chinatown",        to_minutes(14,30), to_minutes(19,0),  120),
    Friend("Steven",    "Russian Hill",     to_minutes(14,0),  to_minutes(20,0),  30),
    Friend("Elizabeth", "Alamo Square",     to_minutes(13,0),  to_minutes(17,15), 120),
    Friend("William",   "Bayview",          to_minutes(18,15), to_minutes(20,15), 90),
]

start_location = "Richmond District"
start_time = to_minutes(9,0)

# Build quick name->Friend map
friend_by_name = {f.name: f for f in friends}

best_solution = {
    "count": 0,
    "end_time": float('inf'),
    "total_travel": float('inf'),
    "itinerary": []  # list of tuples (name, location, start, end)
}

def feasible_from_state(current_loc: str, current_time: int, remaining: List[Friend]) -> List[Tuple[Friend, int, int, int]]:
    feas = []
    for f in remaining:
        t_travel = travel[current_loc][f.location]
        arrival = current_time + t_travel
        start = max(arrival, f.start)
        end = start + f.min_duration
        if end <= f.end:
            feas.append((f, start, end, t_travel))
    return feas

def dfs(current_loc: str, current_time: int, visited_mask: int, order: List[Tuple[str, str, int, int]], total_travel: int):
    global best_solution
    remaining = []
    for i, f in enumerate(friends):
        if not (visited_mask & (1 << i)):
            remaining.append(f)
    feas = feasible_from_state(current_loc, current_time, remaining)

    # Upper bound prune
    current_count = bin(visited_mask).count("1")
    if current_count + len(feas) < best_solution["count"]:
        return

    if not feas:
        # Leaf: update best if better
        if (current_count > best_solution["count"] or
            (current_count == best_solution["count"] and (current_time < best_solution["end_time"] or
             (current_time == best_solution["end_time"] and total_travel < best_solution["total_travel"])))):
            best_solution = {
                "count": current_count,
                "end_time": current_time,
                "total_travel": total_travel,
                "itinerary": order[:]
            }
        return

    # Sort candidates by earliest end of availability to prioritize tight windows
    feas.sort(key=lambda x: (x[0].end, x[1]))  # by window end, then meeting start

    for f, start_m, end_m, t_travel in feas:
        idx = friends.index(f)
        new_mask = visited_mask | (1 << idx)
        order.append((f.name, f.location, start_m, end_m))
        dfs(f.location, end_m, new_mask, order, total_travel + t_travel)
        order.pop()

# Start search
dfs(start_location, start_time, 0, [], 0)

# Build JSON output
output = {"itinerary": []}
for name, loc, start_m, end_m in best_solution["itinerary"]:
    output["itinerary"].append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": fmt_time(start_m),
        "end_time": fmt_time(end_m)
    })

print(json.dumps(output, ensure_ascii=False))