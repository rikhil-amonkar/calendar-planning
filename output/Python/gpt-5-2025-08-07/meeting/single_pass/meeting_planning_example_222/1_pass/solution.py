import itertools
import json

# Helper functions for time handling
def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def to_timestr(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Nob Hill"
start_time_str = "9:00"

people = [
    {
        "name": "Helen",
        "location": "North Beach",
        "avail_start": "7:00",
        "avail_end": "16:45",
        "min_duration": 120
    },
    {
        "name": "Kimberly",
        "location": "Fisherman's Wharf",
        "avail_start": "16:30",
        "avail_end": "21:00",
        "min_duration": 45
    },
    {
        "name": "Patricia",
        "location": "Bayview",
        "avail_start": "18:00",
        "avail_end": "21:15",
        "min_duration": 120
    }
]

# Travel times (minutes)
locations = ["Nob Hill", "North Beach", "Fisherman's Wharf", "Bayview"]
travel_times = {
    "Nob Hill": {
        "North Beach": 8,
        "Fisherman's Wharf": 11,
        "Bayview": 19
    },
    "North Beach": {
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Bayview": 22
    },
    "Fisherman's Wharf": {
        "Nob Hill": 11,
        "North Beach": 6,
        "Bayview": 26
    },
    "Bayview": {
        "Nob Hill": 20,
        "North Beach": 21,
        "Fisherman's Wharf": 25
    }
}
# Ensure 0 travel for same-location
for a in locations:
    travel_times.setdefault(a, {})
    travel_times[a].setdefault(a, 0)

# Preprocess times
start_time = to_minutes(start_time_str)
people_data = {}
for p in people:
    people_data[p["name"]] = {
        "location": p["location"],
        "avail_start": to_minutes(p["avail_start"]),
        "avail_end": to_minutes(p["avail_end"]),
        "min_duration": p["min_duration"]
    }

# Dynamic programming to schedule a fixed order
def schedule_for_order(order_names):
    # Memoization dict: key = (i, loc_prev, time_prev)
    memo = {}

    def dp(i, loc_prev, time_prev):
        key = (i, loc_prev, time_prev)
        if key in memo:
            return memo[key]

        if i == len(order_names):
            # No more people; feasible with zero meeting time
            res = {
                "feasible": True,
                "total_meet": 0,
                "total_wait": 0,
                "itinerary": []
            }
            memo[key] = res
            return res

        name = order_names[i]
        pdata = people_data[name]
        loc_i = pdata["location"]
        travel = travel_times[loc_prev][loc_i]
        arrival = time_prev + travel
        s = max(arrival, pdata["avail_start"])
        wait_i = max(0, s - arrival)
        dur_min = pdata["min_duration"]
        end_min = s + dur_min
        end_max = pdata["avail_end"]

        if end_min > end_max:
            res = {"feasible": False}
            memo[key] = res
            return res

        best = None

        # Iterate end times from latest to earliest to favor later end (ties)
        for e in range(end_max, end_min - 1, -1):
            nxt = dp(i + 1, loc_i, e)
            if not nxt.get("feasible", False):
                continue
            total_meet = (e - s) + nxt["total_meet"]
            total_wait = wait_i + nxt["total_wait"]
            candidate = {
                "feasible": True,
                "total_meet": total_meet,
                "total_wait": total_wait,
                "itinerary": [{"action": "meet",
                               "location": loc_i,
                               "person": name,
                               "start": s,
                               "end": e}] + nxt["itinerary"]
            }
            if best is None:
                best = candidate
            else:
                # Prefer higher total meeting time, then lower total wait
                if (candidate["total_meet"] > best["total_meet"]) or \
                   (candidate["total_meet"] == best["total_meet"] and candidate["total_wait"] < best["total_wait"]):
                    best = candidate

        if best is None:
            best = {"feasible": False}

        memo[key] = best
        return best

    result = dp(0, start_location, start_time)
    return result

# Evaluate all subsets and permutations
all_names = [p["name"] for p in people]

best_overall = None

def compute_travel_sum(order_names):
    total = 0
    loc_prev = start_location
    for name in order_names:
        loc_i = people_data[name]["location"]
        total += travel_times[loc_prev][loc_i]
        loc_prev = loc_i
    return total

# Try largest subsets first
for r in range(len(all_names), 0, -1):
    any_feasible = False
    for subset in itertools.combinations(all_names, r):
        for perm in itertools.permutations(subset):
            sched = schedule_for_order(list(perm))
            if sched.get("feasible", False):
                any_feasible = True
                travel_sum = compute_travel_sum(list(perm))
                # Build score tuple: (num_people, total_meet, -total_wait, -travel_sum)
                score = (len(perm), sched["total_meet"], -sched["total_wait"], -travel_sum)
                candidate = {
                    "score": score,
                    "itinerary": sched["itinerary"],
                    "order": list(perm),
                    "travel_sum": travel_sum
                }
                if best_overall is None or candidate["score"] > best_overall["score"]:
                    best_overall = candidate
    if any_feasible:
        break  # Found optimal count; no need to check smaller subsets

# Build output JSON
output = {"itinerary": []}
if best_overall is not None:
    for item in best_overall["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": to_timestr(item["start"]),
            "end_time": to_timestr(item["end"])
        })

print(json.dumps(output, ensure_ascii=False))