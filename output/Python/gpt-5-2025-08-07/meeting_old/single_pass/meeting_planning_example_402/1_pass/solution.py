import itertools
import json

# Helper functions for time conversion
def to_minutes(t):
    # t like '9:00' or '14:15'
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_timestr(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables: travel times (in minutes)
locations = [
    "Golden Gate Park",
    "Haight-Ashbury",
    "Sunset District",
    "Marina District",
    "Financial District",
    "Union Square",
]

travel = {loc: {} for loc in locations}
# Golden Gate Park to ...
travel["Golden Gate Park"]["Haight-Ashbury"] = 7
travel["Golden Gate Park"]["Sunset District"] = 10
travel["Golden Gate Park"]["Marina District"] = 16
travel["Golden Gate Park"]["Financial District"] = 26
travel["Golden Gate Park"]["Union Square"] = 22
# Haight-Ashbury to ...
travel["Haight-Ashbury"]["Golden Gate Park"] = 7
travel["Haight-Ashbury"]["Sunset District"] = 15
travel["Haight-Ashbury"]["Marina District"] = 17
travel["Haight-Ashbury"]["Financial District"] = 21
travel["Haight-Ashbury"]["Union Square"] = 17
# Sunset District to ...
travel["Sunset District"]["Golden Gate Park"] = 11
travel["Sunset District"]["Haight-Ashbury"] = 15
travel["Sunset District"]["Marina District"] = 21
travel["Sunset District"]["Financial District"] = 30
travel["Sunset District"]["Union Square"] = 30
# Marina District to ...
travel["Marina District"]["Golden Gate Park"] = 18
travel["Marina District"]["Haight-Ashbury"] = 16
travel["Marina District"]["Sunset District"] = 19
travel["Marina District"]["Financial District"] = 17
travel["Marina District"]["Union Square"] = 16
# Financial District to ...
travel["Financial District"]["Golden Gate Park"] = 23
travel["Financial District"]["Haight-Ashbury"] = 19
travel["Financial District"]["Sunset District"] = 31
travel["Financial District"]["Marina District"] = 15
travel["Financial District"]["Union Square"] = 9
# Union Square to ...
travel["Union Square"]["Golden Gate Park"] = 22
travel["Union Square"]["Haight-Ashbury"] = 18
travel["Union Square"]["Sunset District"] = 26
travel["Union Square"]["Marina District"] = 18
travel["Union Square"]["Financial District"] = 9

# Participants constraints
people = {
    "Sarah": {
        "location": "Haight-Ashbury",
        "start": to_minutes("17:00"),
        "end": to_minutes("21:30"),
        "min_duration": 105,
    },
    "Patricia": {
        "location": "Sunset District",
        "start": to_minutes("17:00"),
        "end": to_minutes("19:45"),
        "min_duration": 45,
    },
    "Matthew": {
        "location": "Marina District",
        "start": to_minutes("9:15"),
        "end": to_minutes("12:00"),
        "min_duration": 15,
    },
    "Joseph": {
        "location": "Financial District",
        "start": to_minutes("14:15"),
        "end": to_minutes("18:45"),
        "min_duration": 30,
    },
    "Robert": {
        "location": "Union Square",
        "start": to_minutes("10:15"),
        "end": to_minutes("21:45"),
        "min_duration": 15,
    },
}

# Start conditions
start_location = "Golden Gate Park"
start_time = to_minutes("9:00")

def schedule_order(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0
    total_travel = 0

    for person in order:
        info = people[person]
        loc = info["location"]
        a = info["start"]
        b = info["end"]
        d = info["min_duration"]

        # Travel time; if missing, cannot travel (should not happen with given data)
        t_travel = travel[current_loc].get(loc, None)
        if t_travel is None:
            return None  # missing travel path

        arrival = current_time + t_travel
        start_meet = max(arrival, a)
        if start_meet + d > b:
            return None  # cannot meet within window

        wait_here = max(0, start_meet - arrival)
        total_wait += wait_here
        total_travel += t_travel

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": to_timestr(start_meet),
            "end_time": to_timestr(start_meet + d),
        })

        current_loc = loc
        current_time = start_meet + d

    # Metrics to support tie-breakers
    end_time_of_day = current_time
    metrics = {
        "itinerary": itinerary,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "end_time": end_time_of_day,
    }
    return metrics

def choose_best_schedule():
    names = list(people.keys())
    best = None
    best_count = -1

    # Search subsets by descending size to maximize number of meetings
    for r in range(len(names), -1, -1):
        found_for_r = None
        for subset in itertools.combinations(names, r):
            for perm in itertools.permutations(subset):
                res = schedule_order(perm)
                if res is None:
                    continue
                # Found feasible schedule for this subset
                count = len(res["itinerary"])
                # Count should equal r, but check anyway
                if count != r:
                    continue
                # Update best by tie-breakers:
                # 1) earliest end_time
                # 2) minimum total_wait
                # 3) minimum total_travel
                if found_for_r is None:
                    found_for_r = res
                else:
                    a = res
                    b = found_for_r
                    if (a["end_time"], a["total_wait"], a["total_travel"]) < (b["end_time"], b["total_wait"], b["total_travel"]):
                        found_for_r = a
        if found_for_r is not None:
            best = found_for_r
            best_count = r
            break

    return best

best_schedule = choose_best_schedule()

# Prepare output JSON
output = {
    "itinerary": best_schedule["itinerary"] if best_schedule else []
}

print(json.dumps(output, ensure_ascii=False))