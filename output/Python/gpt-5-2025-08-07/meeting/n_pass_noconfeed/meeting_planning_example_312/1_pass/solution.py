import itertools
import json

# SOLUTION:
# This script computes an optimal meeting schedule given travel times and availability windows.

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables: Travel times (directed, in minutes)
travel = {
    "Richmond District": {
        "Sunset District": 11,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Golden Gate Park": 9,
    },
    "Sunset District": {
        "Richmond District": 12,
        "Haight-Ashbury": 15,
        "Mission District": 24,
        "Golden Gate Park": 11,
    },
    "Haight-Ashbury": {
        "Richmond District": 10,
        "Sunset District": 15,
        "Mission District": 11,
        "Golden Gate Park": 7,
    },
    "Mission District": {
        "Richmond District": 20,
        "Sunset District": 24,
        "Haight-Ashbury": 12,
        "Golden Gate Park": 17,
    },
    "Golden Gate Park": {
        "Richmond District": 7,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Mission District": 17,
    },
}

# Start conditions
start_location = "Richmond District"
start_time_str = "9:00"
start_time = to_minutes(start_time_str)

# Friends' availability and minimum meeting durations (in minutes)
friends = [
    {
        "person": "Sarah",
        "location": "Sunset District",
        "window_start": to_minutes("10:45"),
        "window_end": to_minutes("19:00"),
        "min_duration": 30,
    },
    {
        "person": "Richard",
        "location": "Haight-Ashbury",
        "window_start": to_minutes("11:45"),
        "window_end": to_minutes("15:45"),
        "min_duration": 90,
    },
    {
        "person": "Elizabeth",
        "location": "Mission District",
        "window_start": to_minutes("11:00"),
        "window_end": to_minutes("17:15"),
        "min_duration": 120,
    },
    {
        "person": "Michelle",
        "location": "Golden Gate Park",
        "window_start": to_minutes("18:15"),
        "window_end": to_minutes("20:45"),
        "min_duration": 90,
    },
]

def schedule_for_order(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0
    total_travel = 0
    total_meet = 0

    for i, fr in enumerate(order):
        # Travel to friend's location
        if current_loc == fr["location"]:
            travel_time = 0
        else:
            travel_time = travel[current_loc][fr["location"]]
        arrival_time = current_time + travel_time
        total_travel += travel_time

        # Determine meeting start respecting availability window and arrival
        earliest_start = max(arrival_time, fr["window_start"])
        latest_start = fr["window_end"] - fr["min_duration"]

        if earliest_start > latest_start:
            return None  # infeasible

        # Greedy: start as early as possible
        meet_start = earliest_start

        # Optional lookahead to reduce waiting before the next meeting (clamped)
        if i < len(order) - 1:
            nxt = order[i + 1]
            # Time needed between end of this meeting and the next start window
            t_between = travel[fr["location"]][nxt["location"]]
            # Try to align arrival to the next just-in-time for their window start
            desired_start = nxt["window_start"] - t_between - fr["min_duration"]
            if desired_start < earliest_start:
                desired_start = earliest_start
            if desired_start > latest_start:
                desired_start = latest_start
            meet_start = desired_start

        wait_here = max(0, meet_start - arrival_time)
        total_wait += wait_here

        meet_end = meet_start + fr["min_duration"]
        if meet_end > fr["window_end"]:
            return None  # infeasible

        total_meet += fr["min_duration"]
        itinerary.append({
            "action": "meet",
            "location": fr["location"],
            "person": fr["person"],
            "start_time": to_time_str(meet_start),
            "end_time": to_time_str(meet_end),
        })

        current_loc = fr["location"]
        current_time = meet_end

    return {
        "itinerary": itinerary,
        "stats": {
            "meetings": len(itinerary),
            "finish_time": current_time,
            "total_wait": total_wait,
            "total_travel": total_travel,
            "total_meet": total_meet,
        }
    }

def optimize_schedule(friends_list):
    best = None
    best_score = None

    # Explore all subsets and permutations to maximize meetings
    n = len(friends_list)
    for r in range(n, 0, -1):
        for subset in itertools.combinations(friends_list, r):
            for perm in itertools.permutations(subset):
                result = schedule_for_order(list(perm))
                if not result:
                    continue
                stats = result["stats"]
                # Primary: maximize number of meetings
                # Secondary: minimize total waiting, then minimize finish time, then minimize total travel
                score = (
                    stats["meetings"],
                    -stats["total_wait"],
                    -stats["finish_time"],
                    -stats["total_travel"],
                )
                if (best_score is None) or (score > best_score):
                    best = result
                    best_score = score

        # Early exit if we already found a feasible schedule with r meetings,
        # since we're iterating r from n downwards
        if best and best["stats"]["meetings"] == r:
            break

    return best

result = optimize_schedule(friends)

# Prepare JSON output
output = {
    "itinerary": result["itinerary"] if result else []
}

print(json.dumps(output, ensure_ascii=False))