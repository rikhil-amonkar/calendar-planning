import itertools
import json

# -----------------------------
# Input parameters (constraints)
# -----------------------------

arrival_location = "North Beach"
arrival_time_str = "9:00"

travel_times = {
    ("North Beach", "Mission District"): 18,
    ("Mission District", "North Beach"): 17,
    ("North Beach", "The Castro"): 22,
    ("The Castro", "North Beach"): 20,
    ("Mission District", "The Castro"): 7,
    ("The Castro", "Mission District"): 7,
}

people = [
    {
        "name": "James",
        "location": "Mission District",
        "avail_start": "12:45",
        "avail_end": "14:00",
        "min_minutes": 75,
    },
    {
        "name": "Robert",
        "location": "The Castro",
        "avail_start": "12:45",
        "avail_end": "15:15",
        "min_minutes": 30,
    },
]

# -----------------------------
# Utility functions
# -----------------------------

def to_minutes(hmm: str) -> int:
    h, m = hmm.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel(from_loc: str, to_loc: str) -> int:
    if from_loc == to_loc:
        return 0
    return travel_times[(from_loc, to_loc)]

# Preprocess times
arrival_time = to_minutes(arrival_time_str)
for p in people:
    p["avail_start_min"] = to_minutes(p["avail_start"])
    p["avail_end_min"] = to_minutes(p["avail_end"])

# -----------------------------
# Scheduling search
# -----------------------------

def plan_for_order(order, start_loc, start_time):
    # Recursive DFS over start times and durations per meeting
    best = {
        "score": (-1, -1, float("inf"), float("inf")),  # (friends_met, total_meeting, total_travel, total_wait)
        "itinerary": [],
    }

    def dfs(idx, cur_loc, cur_time, itinerary, total_meeting, total_travel, total_wait):
        nonlocal best
        if idx == len(order):
            score = (len(itinerary), total_meeting, -total_travel, -total_wait)
            if score > best["score"]:
                best = {
                    "score": score,
                    "itinerary": list(itinerary),
                }
            return

        person = order[idx]
        travel = get_travel(cur_loc, person["location"])
        arrival = cur_time + travel

        # Feasible start interval
        earliest_start = max(arrival, person["avail_start_min"])
        latest_start = person["avail_end_min"] - person["min_minutes"]

        if earliest_start > latest_start:
            # Not feasible at all
            return

        # Iterate over possible start times
        # Strategy: consider all starts from earliest to latest (minute resolution)
        for start in range(earliest_start, latest_start + 1):
            min_dur = person["min_minutes"]
            max_dur = person["avail_end_min"] - start
            # To explore different schedules, consider both minimal and maximal duration, and a middle option
            # but ensure uniqueness and feasibility
            candidate_durations = {min_dur, max_dur}
            mid = (min_dur + max_dur) // 2
            candidate_durations.add(mid)
            # Also include a few spaced options to truly consider variety without exploding
            for extra in (15, 30, 45, 60):
                if min_dur + extra <= max_dur:
                    candidate_durations.add(min_dur + extra)
            # Ensure boundaries
            durations = sorted(d for d in candidate_durations if min_dur <= d <= max_dur)

            wait = max(0, start - arrival)

            for dur in durations:
                end = start + dur
                # Proceed to next
                itinerary.append({
                    "action": "meet",
                    "location": person["location"],
                    "person": person["name"],
                    "start_time": start,
                    "end_time": end,
                })
                dfs(
                    idx + 1,
                    person["location"],
                    end,
                    itinerary,
                    total_meeting + dur,
                    total_travel + travel,
                    total_wait + wait
                )
                itinerary.pop()

    dfs(0, start_loc, start_time, [], 0, 0, 0)
    return best

# Build all subsets and orders, prioritize larger subsets first
all_people = people
best_overall = {
    "score": (-1, -1, float("inf"), float("inf")),
    "itinerary": [],
}

# Generate subsets by size descending
for r in range(len(all_people), -1, -1):
    for subset in itertools.combinations(all_people, r):
        # Explore all permutations (orders)
        for order in itertools.permutations(subset):
            result = plan_for_order(order, arrival_location, arrival_time)
            if result["itinerary"]:
                score = result["score"]
                if score > best_overall["score"]:
                    best_overall = result
    # If we already achieved meeting r people, we can stop looking at smaller subsets
    if best_overall["score"][0] == r and r > 0:
        break

# If we found multiple with same count and tie-breaks, best_overall holds the best by score definition
final_itinerary = []
for item in best_overall["itinerary"]:
    final_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start_time"]),
        "end_time": fmt_time(item["end_time"]),
    })

output = {
    "itinerary": final_itinerary
}

print(json.dumps(output, ensure_ascii=False))