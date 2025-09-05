import itertools
import json
import re

# Utility functions for time parsing/formatting
def parse_time_12h(s):
    m = re.match(r'^\s*(\d{1,2}):(\d{2})\s*([AP]M)\s*$', s, re.IGNORECASE)
    if not m:
        raise ValueError(f"Invalid time format: {s}")
    h = int(m.group(1))
    minutes = int(m.group(2))
    ampm = m.group(3).upper()
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:  # PM
        if h != 12:
            h += 12
    return h * 60 + minutes

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters (constraints)
start_location = "Bayview"
arrival_time_str = "9:00AM"

people = [
    {"name": "Barbara",  "location": "North Beach",    "start": "1:45PM", "end": "8:15PM", "min_duration": 60},
    {"name": "Margaret", "location": "Presidio",       "start": "10:15AM","end": "3:15PM","min_duration": 30},
    {"name": "Kevin",    "location": "Haight-Ashbury", "start": "8:00PM", "end": "8:45PM","min_duration": 30},
    {"name": "Kimberly", "location": "Union Square",   "start": "7:45AM", "end": "4:45PM","min_duration": 30},
]

# Travel times (in minutes), directional
travel = {
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Union Square"): 17,

    ("North Beach", "Bayview"): 22,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,

    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Union Square"): 22,

    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 17,

    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18,
}

# Preprocess times to minutes
arrival_time = parse_time_12h(arrival_time_str)
for p in people:
    p["start_min"] = parse_time_12h(p["start"])
    p["end_min"] = parse_time_12h(p["end"])

def compute_schedule(order):
    """
    Given an ordered list of people (dicts), compute a feasible schedule that:
    - Accounts for travel time
    - Meets each person for at least their minimum duration
    - Optionally delays starts (within availability) to reduce early arrival at next window
    Returns dict with feasible flag, itinerary, end_time, total_travel, total_wait
    """
    current_loc = start_location
    t = arrival_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    feasible = True

    for i, person in enumerate(order):
        # Travel to person's location
        key = (current_loc, person["location"])
        if key not in travel:
            feasible = False
            break
        d = travel[key]
        total_travel += d
        arrival = t + d

        # Determine earliest and latest feasible start times
        earliest = max(arrival, person["start_min"])
        latest_start = person["end_min"] - person["min_duration"]
        if earliest > latest_start:
            feasible = False
            break

        # Choose start time
        if i < len(order) - 1:
            nxt = order[i + 1]
            d_to_next = travel[(person["location"], nxt["location"])]
            desired = nxt["start_min"] - d_to_next - person["min_duration"]
            start_time = max(earliest, min(desired, latest_start))
        else:
            # For the last meeting, take the earliest feasible start to minimize end time
            start_time = earliest

        # Wait if arrived early
        wait = max(0, start_time - arrival)
        total_wait += wait

        end_time = start_time + person["min_duration"]

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": fmt_time(start_time),
            "end_time": fmt_time(end_time),
        })

        # Advance state
        t = end_time
        current_loc = person["location"]

    final_end_time = t
    return {
        "feasible": feasible,
        "itinerary": itinerary if feasible else [],
        "end_time": final_end_time if feasible else None,
        "total_travel": total_travel if feasible else None,
        "total_wait": total_wait if feasible else None,
        "meet_count": len(order) if feasible else 0
    }

def optimize_schedule():
    best = None
    best_plan = None

    # Try larger subsets first to maximize number of meetings
    for r in range(len(people), 0, -1):
        found_any = False
        for subset in itertools.combinations(people, r):
            for perm in itertools.permutations(subset):
                plan = compute_schedule(list(perm))
                if not plan["feasible"]:
                    continue
                found_any = True
                # Objective: maximize meetings, then minimize end_time, then travel, then waiting
                obj = (
                    -plan["meet_count"],
                    plan["end_time"],
                    plan["total_travel"],
                    plan["total_wait"],
                )
                if best is None or obj < best:
                    best = obj
                    best_plan = plan
        if found_any:
            break

    if best_plan is None:
        return {"itinerary": []}
    else:
        return {"itinerary": best_plan["itinerary"]}

def main():
    result = optimize_schedule()
    print(json.dumps(result))

if __name__ == "__main__":
    main()