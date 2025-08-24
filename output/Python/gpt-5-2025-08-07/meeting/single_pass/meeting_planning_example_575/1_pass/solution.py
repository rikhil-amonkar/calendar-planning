"""
SOLUTION:
"""

import itertools
import json

# Utility functions for time handling
def parse_time(tstr):
    # Handles formats like '9:00AM', '6:15PM'
    tstr = tstr.strip().upper()
    meridian = None
    if tstr.endswith("AM") or tstr.endswith("PM"):
        meridian = tstr[-2:]
        tstr = tstr[:-2]
    h, m = tstr.split(":")
    h = int(h)
    m = int(m)
    if meridian == "AM":
        if h == 12:
            h = 0
    elif meridian == "PM":
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Input parameters

start_location = "The Castro"
start_time_str = "9:00AM"
start_time = parse_time(start_time_str)

# Travel times (in minutes), directed
travel = {
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Russian Hill"): 18,

    ("Presidio", "The Castro"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Russian Hill"): 14,

    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Russian Hill"): 24,

    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Russian Hill"): 17,

    ("Mission District", "The Castro"): 7,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Russian Hill"): 15,

    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Russian Hill"): 19,

    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Golden Gate Park"): 21,
}

# People constraints
people = {
    "Rebecca": {
        "location": "Presidio",
        "start": parse_time("6:15PM"),
        "end": parse_time("8:45PM"),
        "min_meet": 60
    },
    "Linda": {
        "location": "Sunset District",
        "start": parse_time("3:30PM"),
        "end": parse_time("7:45PM"),
        "min_meet": 30
    },
    "Elizabeth": {
        "location": "Haight-Ashbury",
        "start": parse_time("5:15PM"),
        "end": parse_time("7:30PM"),
        "min_meet": 105
    },
    "William": {
        "location": "Mission District",
        "start": parse_time("1:15PM"),
        "end": parse_time("7:30PM"),
        "min_meet": 30
    },
    "Robert": {
        "location": "Golden Gate Park",
        "start": parse_time("2:15PM"),
        "end": parse_time("9:30PM"),
        "min_meet": 45
    },
    "Mark": {
        "location": "Russian Hill",
        "start": parse_time("10:00AM"),
        "end": parse_time("9:15PM"),
        "min_meet": 75
    },
}

# Scheduling engine
def compute_schedule(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        info = people[person]
        loc = info["location"]
        window_start = info["start"]
        window_end = info["end"]
        min_meet = info["min_meet"]

        # Travel time
        if (current_loc, loc) not in travel:
            return None  # No travel path data
        ttime = travel[(current_loc, loc)]
        arrival_time = current_time + ttime

        # Determine feasible start time
        latest_start = window_end - min_meet
        if arrival_time > latest_start:
            return None  # Too late to start meeting
        meet_start = max(arrival_time, window_start)
        if meet_start > latest_start:
            return None  # Even waiting doesn't help

        # Waiting time (if arrival before meeting window/opportunity)
        wait = max(0, meet_start - arrival_time)
        total_wait += wait
        total_travel += ttime

        meet_end = meet_start + min_meet

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": minutes_to_str(meet_start),
            "end_time": minutes_to_str(meet_end),
        })

        # Update state
        current_loc = loc
        current_time = meet_end

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "count": len(order),
    }

def best_schedule():
    names = list(people.keys())
    best = None
    # Try largest number of meetings down to smaller
    for k in range(len(names), 0, -1):
        for perm in itertools.permutations(names, k):
            sched = compute_schedule(perm)
            if sched is None:
                continue
            if best is None:
                best = sched
            else:
                # Prefer more meetings
                if sched["count"] > best["count"]:
                    best = sched
                elif sched["count"] == best["count"]:
                    # Tie-breaker: earliest finish time
                    if sched["finish_time"] < best["finish_time"]:
                        best = sched
                    elif sched["finish_time"] == best["finish_time"]:
                        # Next: less total wait
                        if sched["total_wait"] < best["total_wait"]:
                            best = sched
                        elif sched["total_wait"] == best["total_wait"]:
                            # Next: less total travel
                            if sched["total_travel"] < best["total_travel"]:
                                best = sched
        if best is not None and best["count"] == k:
            # Found at least one schedule at this maximum size; keep searching within same k to improve tie-breakers
            # but if we completed all permutations for this k, we can return
            pass
        # After completing all permutations for this k, if best exists with current k, stop
        if best is not None and best["count"] == k:
            break
    return best

def main():
    sched = best_schedule()
    output = {"itinerary": []}
    if sched:
        output["itinerary"] = sched["itinerary"]
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()