import itertools
import json

def parse_time(t):
    # t like '9:00', '13:30'
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Haight-Ashbury"
arrival_time_str = "9:00"

travel = {
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Alamo Square": 5,
        "Pacific Heights": 12
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Nob Hill": 5,
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Pacific Heights": 7
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Alamo Square": 20,
        "Pacific Heights": 12
    },
    "Nob Hill": {
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "Fisherman's Wharf": 11,
        "Golden Gate Park": 17,
        "Alamo Square": 11,
        "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Russian Hill": 19,
        "Fisherman's Wharf": 24,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "Pacific Heights": 16
    },
    "Alamo Square": {
        "Haight-Ashbury": 5,
        "Russian Hill": 13,
        "Fisherman's Wharf": 19,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Alamo Square": 10
    }
}

people = [
    {
        "name": "Stephanie",
        "location": "Russian Hill",
        "window_start": "20:00",
        "window_end": "20:45",
        "min_minutes": 15
    },
    {
        "name": "Kevin",
        "location": "Fisherman's Wharf",
        "window_start": "19:15",
        "window_end": "21:45",
        "min_minutes": 75
    },
    {
        "name": "Robert",
        "location": "Nob Hill",
        "window_start": "7:45",
        "window_end": "10:30",
        "min_minutes": 90
    },
    {
        "name": "Steven",
        "location": "Golden Gate Park",
        "window_start": "8:30",
        "window_end": "17:00",
        "min_minutes": 75
    },
    {
        "name": "Anthony",
        "location": "Alamo Square",
        "window_start": "7:45",
        "window_end": "19:45",
        "min_minutes": 15
    },
    {
        "name": "Sandra",
        "location": "Pacific Heights",
        "window_start": "14:45",
        "window_end": "21:45",
        "min_minutes": 45
    }
]

# Preprocess windows to minutes
for p in people:
    p["ws"] = parse_time(p["window_start"])
    p["we"] = parse_time(p["window_end"])

start_time = parse_time(arrival_time_str)

def feasible_schedule(order):
    cur_loc = start_location
    cur_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    for person in order:
        loc = person["location"]
        # Travel time
        if cur_loc == loc:
            t_travel = 0
        else:
            # Guard: ensure travel time exists
            if cur_loc not in travel or loc not in travel[cur_loc]:
                return None
            t_travel = travel[cur_loc][loc]
        arrival = cur_time + t_travel
        total_travel += t_travel

        # If arrive before window, wait
        start_meet = max(arrival, person["ws"])
        wait_time = max(0, person["ws"] - arrival)
        total_wait += wait_time

        end_meet = start_meet + person["min_minutes"]

        # Must end by window end
        if end_meet > person["we"]:
            return None

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person["name"],
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet)
        })

        cur_loc = loc
        cur_time = end_meet

    finish_time = cur_time
    return {
        "itinerary": itinerary,
        "count": len(order),
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait
    }

# Search all subsets and permutations to maximize number of friends met
best = None

n = len(people)
# Iterate by descending subset size to prioritize meeting more friends
for r in range(n, 0, -1):
    found_for_r = False
    for subset in itertools.combinations(people, r):
        # Permute each subset
        for perm in itertools.permutations(subset):
            sched = feasible_schedule(perm)
            if sched is None:
                continue
            # Update best with tie-breakers:
            # 1) Max count
            # 2) Earliest finish_time
            # 3) Minimal total_travel
            # 4) Minimal total_wait
            if best is None:
                best = sched
                found_for_r = True
            else:
                if sched["count"] > best["count"]:
                    best = sched
                    found_for_r = True
                elif sched["count"] == best["count"]:
                    if sched["finish_time"] < best["finish_time"]:
                        best = sched
                        found_for_r = True
                    elif sched["finish_time"] == best["finish_time"]:
                        if sched["total_travel"] < best["total_travel"]:
                            best = sched
                            found_for_r = True
                        elif sched["total_travel"] == best["total_travel"]:
                            if sched["total_wait"] < best["total_wait"]:
                                best = sched
                                found_for_r = True
    if found_for_r:
        # Since we iterate r descending, first r with any feasible schedule is optimal in count
        break

# Ensure output JSON structure
output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output, ensure_ascii=False))