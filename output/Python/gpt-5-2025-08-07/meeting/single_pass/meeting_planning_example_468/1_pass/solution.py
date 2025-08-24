import itertools
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times in minutes between locations
travel = {
    "The Castro": {
        "Bayview": 19,
        "Pacific Heights": 16,
        "Alamo Square": 8,
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
    },
    "Bayview": {
        "The Castro": 20,
        "Pacific Heights": 23,
        "Alamo Square": 16,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Bayview": 22,
        "Alamo Square": 10,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15,
    },
    "Alamo Square": {
        "The Castro": 8,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 9,
    },
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Alamo Square": 20,
        "Golden Gate Park": 25,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Alamo Square": 10,
        "Fisherman's Wharf": 24,
    },
}

# Meeting constraints
friends = [
    {
        "name": "Rebecca",
        "location": "Bayview",
        "start": minutes(9, 0),
        "end": minutes(12, 45),
        "min_dur": 90,
    },
    {
        "name": "Amanda",
        "location": "Pacific Heights",
        "start": minutes(18, 30),
        "end": minutes(21, 45),
        "min_dur": 90,
    },
    {
        "name": "James",
        "location": "Alamo Square",
        "start": minutes(9, 45),
        "end": minutes(21, 15),
        "min_dur": 90,
    },
    {
        "name": "Sarah",
        "location": "Fisherman's Wharf",
        "start": minutes(8, 0),
        "end": minutes(21, 30),
        "min_dur": 90,
    },
    {
        "name": "Melissa",
        "location": "Golden Gate Park",
        "start": minutes(9, 0),
        "end": minutes(18, 45),
        "min_dur": 90,
    },
]

start_location = "The Castro"
start_time = minutes(9, 0)

def evaluate_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    idle_total = 0
    count = 0

    for i, f in enumerate(order):
        # Travel to friend
        travel_time = travel[current_loc][f["location"]]
        arrival = current_time + travel_time

        # Meeting start must respect window
        start_mt = max(arrival, f["start"])
        if start_mt > f["end"] - f["min_dur"]:
            # Cannot fit minimum duration for this friend
            break

        # Idle waiting time at arrival (if any)
        if arrival < f["start"]:
            idle_total += (f["start"] - arrival)

        # Minimum end after required duration
        earliest_end = start_mt + f["min_dur"]

        # Optionally extend meeting to reduce waiting for next friend
        if i < len(order) - 1:
            nxt = order[i + 1]
            travel_next = travel[f["location"]][nxt["location"]]
            earliest_arrival_next = earliest_end + travel_next
            latest_start_next = nxt["end"] - nxt["min_dur"]

            # If it's already impossible to meet next even with earliest departure, we still finalize this meeting and will break on next iteration.
            extra_extension = 0
            # If we would arrive before next's window opens, extend current meet to bridge the gap if possible
            if earliest_arrival_next < nxt["start"]:
                max_extend = f["end"] - earliest_end
                needed = nxt["start"] - earliest_arrival_next
                extra_extension = min(max_extend, needed)
            end_mt = earliest_end + extra_extension
        else:
            end_mt = earliest_end

        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": fmt_time(start_mt),
            "end_time": fmt_time(end_mt),
        })

        # Update state
        current_time = end_mt
        current_loc = f["location"]
        count += 1

    finish_time = current_time
    return {
        "count": count,
        "idle": idle_total,
        "finish": finish_time,
        "itinerary": itinerary,
    }

best = None
best_score = None

for order in itertools.permutations(friends):
    result = evaluate_order(order)
    score = (-result["count"], result["idle"], result["finish"])  # maximize count, minimize idle, minimize finish time
    if best is None or score < best_score:
        best = result
        best_score = score
    # Early exit if perfect schedule meeting everyone found with zero idle and earliest finish (cannot beat)
    if result["count"] == len(friends) and result["idle"] == 0:
        # Earliest possible finish cannot be earlier than 20:00 due to Amanda's 90 min starting 18:30
        # We can still keep searching, but this is already optimal enough; we can break to save time.
        pass

output = {
    "itinerary": best["itinerary"]
}

print(json.dumps(output, indent=2))