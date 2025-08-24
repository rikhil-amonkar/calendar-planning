"""SOLUTION:"""
import json
from typing import Dict, Tuple, List

# Helper functions
def to_minutes(h: int, m: int = 0) -> int:
    return h * 60 + m

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
start_location = "Financial District"
start_time = to_minutes(9, 0)  # 9:00

# Travel times in minutes between locations
travel: Dict[str, Dict[str, int]] = {
    "Financial District": {
        "Chinatown": 5,
        "Alamo Square": 17,
        "Bayview": 19,
        "Fisherman's Wharf": 10
    },
    "Chinatown": {
        "Financial District": 5,
        "Alamo Square": 17,
        "Bayview": 22,
        "Fisherman's Wharf": 8
    },
    "Alamo Square": {
        "Financial District": 17,
        "Chinatown": 16,
        "Bayview": 16,
        "Fisherman's Wharf": 19
    },
    "Bayview": {
        "Financial District": 19,
        "Chinatown": 18,
        "Alamo Square": 16,
        "Fisherman's Wharf": 25
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Chinatown": 12,
        "Alamo Square": 20,
        "Bayview": 26
    }
}

# Friends' availability and minimum meeting durations
friends = {
    "Nancy": {
        "location": "Chinatown",
        "window": (to_minutes(9, 30), to_minutes(13, 30)),
        "min_meet": 90
    },
    "Mary": {
        "location": "Alamo Square",
        "window": (to_minutes(7, 0), to_minutes(21, 0)),
        "min_meet": 75
    },
    "Jessica": {
        "location": "Bayview",
        "window": (to_minutes(11, 15), to_minutes(13, 45)),
        "min_meet": 45
    },
    "Rebecca": {
        "location": "Fisherman's Wharf",
        "window": (to_minutes(7, 0), to_minutes(8, 30)),
        "min_meet": 45
    }
}

Friend = Tuple[str, Dict[str, object]]

def feasible_meeting(cur_loc: str, cur_time: int, friend_name: str) -> Tuple[int, int, int] or None:
    """Return (travel_time, start_time, end_time) if feasible, else None."""
    info = friends[friend_name]
    loc = info["location"]
    if cur_loc == loc:
        t_travel = 0
    else:
        if cur_loc not in travel or loc not in travel[cur_loc]:
            return None
        t_travel = travel[cur_loc][loc]
    avail_start, avail_end = info["window"]
    min_meet = info["min_meet"]
    # Earliest feasible start is either after travel or at availability start
    start = max(cur_time + t_travel, avail_start)
    end = start + min_meet
    if end <= avail_end:
        return t_travel, start, end
    return None

def dfs(cur_loc: str, cur_time: int, remaining: List[str]) -> Dict:
    # Base best solution: do nothing more
    best = {
        "itinerary": [],
        "total_travel": 0,
        "finish_time": cur_time
    }

    def score(sol: Dict) -> Tuple[int, int, int]:
        # Objective: maximize #meetings, then minimize total travel, then finish earlier
        return (len(sol["itinerary"]), -sol["total_travel"], -sol["finish_time"])

    for fname in remaining:
        feas = feasible_meeting(cur_loc, cur_time, fname)
        if feas is None:
            continue
        t_travel, start_t, end_t = feas
        # Recurse after meeting this friend
        new_remaining = [x for x in remaining if x != fname]
        sub = dfs(friends[fname]["location"], end_t, new_remaining)

        # Build current branch solution
        current_itin = [{
            "action": "meet",
            "location": friends[fname]["location"],
            "person": fname,
            "start_time": fmt_time(start_t),
            "end_time": fmt_time(end_t)
        }] + sub["itinerary"]

        branch = {
            "itinerary": current_itin,
            "total_travel": t_travel + sub["total_travel"],
            "finish_time": sub["finish_time"] if sub["itinerary"] else end_t
        }

        if score(branch) > score(best):
            best = branch

    return best

# Run the search
remaining_friends = list(friends.keys())
solution = dfs(start_location, start_time, remaining_friends)

# Output JSON
output = {"itinerary": solution["itinerary"]}
print(json.dumps(output, ensure_ascii=False))