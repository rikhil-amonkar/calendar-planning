import json
from itertools import permutations, combinations

# Input parameters
start_location = "Financial District"
arrival_time_str = "9:00"

# Travel times in minutes (directed where specified)
travel = {
    "Financial District": {"Chinatown": 5, "Golden Gate Park": 23},
    "Chinatown": {"Financial District": 5, "Golden Gate Park": 23},
    "Golden Gate Park": {"Financial District": 26, "Chinatown": 23},
}
# Ensure complete mapping for any missing same-location entries
for a in travel:
    travel[a][a] = 0

def parse_time(tstr):
    # Expect format like '9:00' or '13:30'
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

arrival_time = parse_time(arrival_time_str)

# Friends and constraints
friends = [
    {
        "name": "Kenneth",
        "location": "Chinatown",
        "window_start": parse_time("12:00"),
        "window_end": parse_time("15:00"),
        "min_duration": 90
    },
    {
        "name": "Barbara",
        "location": "Golden Gate Park",
        "window_start": parse_time("8:15"),
        "window_end": parse_time("19:00"),
        "min_duration": 45
    }
]

# Helper: build dict by name
friend_by_name = {f["name"]: f for f in friends}

def schedule_for_order(order_names):
    # Returns (feasible, itinerary, metrics_dict)
    current_loc = start_location
    current_time = arrival_time
    itinerary = []
    total_idle = 0
    total_travel = 0

    for idx, name in enumerate(order_names):
        p = friend_by_name[name]
        # Travel to person's location
        t_travel = travel[current_loc][p["location"]]
        total_travel += t_travel
        arrival = current_time + t_travel

        # Determine meeting start respecting availability
        start = max(arrival, p["window_start"])
        # Idle waiting before meeting (either at previous location or at meeting location)
        total_idle += max(0, start - arrival)

        # Minimum end time
        min_end = start + p["min_duration"]
        if min_end > p["window_end"]:
            return False, [], {}

        end = min_end

        # If there is a next meeting, consider extending this meeting to reduce waiting
        if idx < len(order_names) - 1:
            next_p = friend_by_name[order_names[idx + 1]]
            t_to_next = travel[p["location"]][next_p["location"]]
            # Earliest arrival at next if we leave immediately after min meeting
            earliest_arr_next = min_end + t_to_next

            # Latest time we can arrive at next to still meet min duration
            next_latest_start = next_p["window_end"] - next_p["min_duration"]
            if earliest_arr_next > next_latest_start:
                # Even with minimal duration now, we arrive too late for next meeting
                return False, [], {}

            # If we'd arrive before next window start, try to extend current meeting
            if earliest_arr_next < next_p["window_start"]:
                slack = next_p["window_start"] - earliest_arr_next
                extend_cap = p["window_end"] - min_end
                extend_by = min(slack, extend_cap)
                end = min_end + extend_by
                # Note: Any residual waiting for next meeting will be accounted for
                # when scheduling the next meeting (as pre-meeting idle time).
        # Append this meeting
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
            "_start_min": start,
            "_end_min": end
        })
        current_time = end
        current_loc = p["location"]

    # Compute finish time, meeting time total
    finish_time = itinerary[-1]["_end_min"] if itinerary else arrival_time
    total_meeting_time = sum(item["_end_min"] - item["_start_min"] for item in itinerary)

    # Clean internal fields from itinerary
    for item in itinerary:
        item.pop("_start_min", None)
        item.pop("_end_min", None)

    metrics = {
        "num_met": len(order_names),
        "total_idle": total_idle,
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_meeting_time": total_meeting_time
    }
    return True, itinerary, metrics

# Explore schedules: prioritize meeting as many friends as possible, then minimize idle, then earliest finish, then minimal travel
best = None  # tuple of (score_tuple, itinerary)
n = len(friends)
friend_names = [f["name"] for f in friends]

# Generate subsets from largest to smallest
for r in range(n, 0, -1):
    found_any_for_this_size = False
    for subset in combinations(friend_names, r):
        for order in permutations(subset):
            feasible, itinerary, metrics = schedule_for_order(order)
            if not feasible:
                continue
            found_any_for_this_size = True
            # Score: more friends first (-num_met for ascending sort), then less idle, then earlier finish, then less travel
            score = (-metrics["num_met"], metrics["total_idle"], metrics["finish_time"], metrics["total_travel"])
            if best is None or score < best[0]:
                best = (score, itinerary, metrics)
    if found_any_for_this_size:
        break  # We found schedules with max number of friends; no need to consider smaller subsets

# If no feasible schedule (shouldn't happen here), output empty itinerary
output = {"itinerary": best[1] if best else []}

print(json.dumps(output))