import json
import itertools

# Helper functions
def hm_to_min(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def min_to_hm(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Input variables: travel times (directed, in minutes)
travel = {
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Golden Gate Park": 11,
        "Mission District": 24,
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Golden Gate Park": 9,
        "Mission District": 10,
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "Mission District": 16,
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Mission District": 17,
    },
    "Mission District": {
        "Sunset District": 24,
        "Alamo Square": 11,
        "Russian Hill": 15,
        "Golden Gate Park": 17,
    },
}

# Input variables: participants constraints
participants = {
    "Charles": {
        "location": "Alamo Square",
        "window_start": hm_to_min("18:00"),
        "window_end": hm_to_min("20:45"),
        "min_duration": 90,
    },
    "Margaret": {
        "location": "Russian Hill",
        "window_start": hm_to_min("9:00"),
        "window_end": hm_to_min("16:00"),
        "min_duration": 30,
    },
    "Daniel": {
        "location": "Golden Gate Park",
        "window_start": hm_to_min("8:00"),
        "window_end": hm_to_min("13:30"),
        "min_duration": 15,
    },
    "Stephanie": {
        "location": "Mission District",
        "window_start": hm_to_min("20:30"),
        "window_end": hm_to_min("22:00"),
        "min_duration": 90,
    },
}

# Start conditions
start_location = "Sunset District"
start_time = hm_to_min("9:00")

def schedule_order(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0
    total_travel = 0

    for person in order:
        info = participants[person]
        loc = info["location"]
        w_start = info["window_start"]
        w_end = info["window_end"]
        dur = info["min_duration"]

        # travel
        if current_loc not in travel or loc not in travel[current_loc]:
            return None  # cannot travel
        t_travel = travel[current_loc][loc]
        arrival = current_time + t_travel
        total_travel += t_travel

        # wait if arriving before window
        start_meet = max(arrival, w_start)
        wait = max(0, start_meet - arrival)
        total_wait += wait

        end_meet = start_meet + dur
        if end_meet > w_end:
            return None  # cannot fit minimum duration in window

        # record
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": min_to_hm(start_meet),
            "end_time": min_to_hm(end_meet),
        })

        # update current
        current_loc = loc
        current_time = end_meet

    return {
        "itinerary": itinerary,
        "finish_time": current_time,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "met_count": len(itinerary),
    }

def find_best_schedule():
    people = list(participants.keys())

    best = None
    # Try all subset sizes from max to min
    for r in range(len(people), 0, -1):
        any_feasible = False
        for subset in itertools.permutations(people, r):
            sched = schedule_order(subset)
            if not sched:
                continue
            any_feasible = True
            if best is None:
                best = sched
            else:
                # Compare: maximize met_count, then minimize total_wait, then minimize finish_time, then total_travel
                if (sched["met_count"] > best["met_count"] or
                    (sched["met_count"] == best["met_count"] and sched["total_wait"] < best["total_wait"]) or
                    (sched["met_count"] == best["met_count"] and sched["total_wait"] == best["total_wait"] and sched["finish_time"] < best["finish_time"]) or
                    (sched["met_count"] == best["met_count"] and sched["total_wait"] == best["total_wait"] and sched["finish_time"] == best["finish_time"] and sched["total_travel"] < best["total_travel"])
                   ):
                    best = sched
        if any_feasible:
            break  # stop after finding best for largest r
    return best

best_schedule = find_best_schedule()

# Output JSON with only the itinerary as required
output = {"itinerary": best_schedule["itinerary"] if best_schedule else []}
print(json.dumps(output, ensure_ascii=False))