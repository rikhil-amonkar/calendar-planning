import json
import itertools

def parse_time(s):
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        time_part = s[:-2]
    else:
        # assume 24-hour format
        ampm = None
        time_part = s
    hour, minute = map(int, time_part.split(":"))
    if ampm == "AM":
        if hour == 12:
            hour = 0
    elif ampm == "PM":
        if hour != 12:
            hour += 12
    return hour * 60 + minute

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) between locations
travel = {
    "Bayview": {
        "Nob Hill": 20,
        "Union Square": 17,
        "Chinatown": 18,
        "The Castro": 20,
        "Presidio": 31,
        "Pacific Heights": 23,
        "Russian Hill": 23,
    },
    "Nob Hill": {
        "Bayview": 19,
        "Union Square": 7,
        "Chinatown": 6,
        "The Castro": 17,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Russian Hill": 5,
    },
    "Union Square": {
        "Bayview": 15,
        "Nob Hill": 9,
        "Chinatown": 7,
        "The Castro": 19,
        "Presidio": 24,
        "Pacific Heights": 15,
        "Russian Hill": 13,
    },
    "Chinatown": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 7,
        "The Castro": 22,
        "Presidio": 19,
        "Pacific Heights": 10,
        "Russian Hill": 7,
    },
    "The Castro": {
        "Bayview": 19,
        "Nob Hill": 16,
        "Union Square": 19,
        "Chinatown": 20,
        "Presidio": 20,
        "Pacific Heights": 16,
        "Russian Hill": 18,
    },
    "Presidio": {
        "Bayview": 31,
        "Nob Hill": 18,
        "Union Square": 22,
        "Chinatown": 21,
        "The Castro": 21,
        "Pacific Heights": 11,
        "Russian Hill": 14,
    },
    "Pacific Heights": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 12,
        "Chinatown": 11,
        "The Castro": 16,
        "Presidio": 11,
        "Russian Hill": 7,
    },
    "Russian Hill": {
        "Bayview": 23,
        "Nob Hill": 5,
        "Union Square": 11,
        "Chinatown": 9,
        "The Castro": 21,
        "Presidio": 14,
        "Pacific Heights": 7,
    },
}

# Meeting constraints
friends = [
    {
        "name": "Paul",
        "location": "Nob Hill",
        "window_start": parse_time("4:15PM"),
        "window_end": parse_time("9:15PM"),
        "min_duration": 60,
    },
    {
        "name": "Carol",
        "location": "Union Square",
        "window_start": parse_time("6:00PM"),
        "window_end": parse_time("8:15PM"),
        "min_duration": 120,
    },
    {
        "name": "Patricia",
        "location": "Chinatown",
        "window_start": parse_time("8:00PM"),
        "window_end": parse_time("9:30PM"),
        "min_duration": 75,
    },
    {
        "name": "Karen",
        "location": "The Castro",
        "window_start": parse_time("5:00PM"),
        "window_end": parse_time("7:00PM"),
        "min_duration": 45,
    },
    {
        "name": "Nancy",
        "location": "Presidio",
        "window_start": parse_time("11:45AM"),
        "window_end": parse_time("10:00PM"),
        "min_duration": 30,
    },
    {
        "name": "Jeffrey",
        "location": "Pacific Heights",
        "window_start": parse_time("8:00PM"),
        "window_end": parse_time("8:45PM"),
        "min_duration": 45,
    },
    {
        "name": "Matthew",
        "location": "Russian Hill",
        "window_start": parse_time("3:45PM"),
        "window_end": parse_time("9:45PM"),
        "min_duration": 75,
    },
]

start_location = "Bayview"
start_time = parse_time("9:00AM")

def schedule_order(order):
    curr_loc = start_location
    curr_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    for f in order:
        loc = f["location"]
        # Travel time from current location to friend's location
        if curr_loc not in travel or loc not in travel[curr_loc]:
            return None  # Missing travel time
        t_travel = travel[curr_loc][loc]
        arrival = curr_time + t_travel
        total_travel += t_travel
        start_meet = max(arrival, f["window_start"])
        # Wait if arrive early
        if start_meet > arrival:
            total_wait += start_meet - arrival
        end_meet = start_meet + f["min_duration"]
        if end_meet > f["window_end"]:
            return None  # Cannot fit meeting within window
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": f["name"],
            "start_time": start_meet,
            "end_time": end_meet
        })
        curr_loc = loc
        curr_time = end_meet
    return {
        "itinerary": itinerary,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "end_time": curr_time
    }

best_solution = None
n = len(friends)

# Search for maximum number of meetings; break ties by:
# 1) minimal total waiting time
# 2) minimal total travel time
# 3) earliest end time
for k in range(n, 0, -1):
    best_for_k = None
    for comb in itertools.combinations(friends, k):
        for perm in itertools.permutations(comb):
            res = schedule_order(perm)
            if res is not None:
                if best_for_k is None:
                    best_for_k = res
                else:
                    # tie-breakers
                    if res["total_wait"] < best_for_k["total_wait"]:
                        best_for_k = res
                    elif res["total_wait"] == best_for_k["total_wait"]:
                        if res["total_travel"] < best_for_k["total_travel"]:
                            best_for_k = res
                        elif res["total_travel"] == best_for_k["total_travel"]:
                            if res["end_time"] < best_for_k["end_time"]:
                                best_for_k = res
    if best_for_k is not None:
        best_solution = best_for_k
        break

output = {"itinerary": []}
if best_solution is not None:
    for item in best_solution["itinerary"]:
        output["itinerary"].append({
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start_time"]),
            "end_time": fmt_time(item["end_time"]),
        })

print(json.dumps(output))