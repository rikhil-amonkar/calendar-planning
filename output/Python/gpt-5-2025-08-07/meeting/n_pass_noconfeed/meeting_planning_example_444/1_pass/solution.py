import itertools
import json

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables: start location and time
start_location = "Financial District"
start_time_str = "9:00"
start_time = time_to_minutes(start_time_str)

# Travel times (directed, in minutes)
travel = {
    "Financial District": {
        "Russian Hill": 10,
        "Sunset District": 31,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23,
    },
    "Russian Hill": {
        "Financial District": 11,
        "Sunset District": 23,
        "North Beach": 5,
        "The Castro": 21,
        "Golden Gate Park": 21,
    },
    "Sunset District": {
        "Financial District": 30,
        "Russian Hill": 24,
        "North Beach": 29,
        "The Castro": 17,
        "Golden Gate Park": 11,
    },
    "North Beach": {
        "Financial District": 8,
        "Russian Hill": 4,
        "Sunset District": 27,
        "The Castro": 22,
        "Golden Gate Park": 22,
    },
    "The Castro": {
        "Financial District": 20,
        "Russian Hill": 18,
        "Sunset District": 17,
        "North Beach": 20,
        "Golden Gate Park": 11,
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Russian Hill": 19,
        "Sunset District": 10,
        "North Beach": 24,
        "The Castro": 13,
    },
}

# People constraints
people = [
    {
        "name": "Ronald",
        "location": "Russian Hill",
        "window_start": time_to_minutes("13:45"),
        "window_end": time_to_minutes("17:15"),
        "min_duration": 105,
    },
    {
        "name": "Patricia",
        "location": "Sunset District",
        "window_start": time_to_minutes("9:15"),
        "window_end": time_to_minutes("22:00"),
        "min_duration": 60,
    },
    {
        "name": "Laura",
        "location": "North Beach",
        "window_start": time_to_minutes("12:30"),
        "window_end": time_to_minutes("12:45"),
        "min_duration": 15,
    },
    {
        "name": "Emily",
        "location": "The Castro",
        "window_start": time_to_minutes("16:15"),
        "window_end": time_to_minutes("18:30"),
        "min_duration": 60,
    },
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "window_start": time_to_minutes("15:00"),
        "window_end": time_to_minutes("16:30"),
        "min_duration": 60,
    },
]

# Helper to simulate a fixed ordered schedule; returns (feasible, meetings, finish_time, total_travel)
def simulate(order):
    current_loc = start_location
    current_time = start_time
    meetings = []
    total_travel = 0

    for person in order:
        loc = person["location"]
        # Travel time from current_loc to loc
        if current_loc not in travel or loc not in travel[current_loc]:
            return False, [], None, None  # missing travel data
        ttime = travel[current_loc][loc]
        arrival = current_time + ttime
        total_travel += ttime

        start = max(arrival, person["window_start"])
        end = start + person["min_duration"]
        if end > person["window_end"]:
            return False, [], None, None  # infeasible
        # Record meeting
        meetings.append({
            "action": "meet",
            "location": loc,
            "person": person["name"],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end),
        })
        # Update state
        current_loc = loc
        current_time = end

    finish_time = current_time
    return True, meetings, finish_time, total_travel

# Explore all subsets and permutations to maximize number of meetings, then tie-breakers
best_meetings = []
best_finish = None
best_travel = None

# Generate all subsets of people (by indices for uniqueness)
all_people = people

for r in range(len(all_people), 0, -1):  # start from largest subsets
    found_better_for_size = False
    for subset in itertools.combinations(all_people, r):
        for perm in itertools.permutations(subset):
            feasible, meetings, finish_time, total_travel = simulate(perm)
            if not feasible:
                continue
            # Update best based on criteria:
            # 1) Max meetings
            # 2) Earliest finish time
            # 3) Minimal total travel time
            if len(meetings) > len(best_meetings):
                best_meetings = meetings
                best_finish = finish_time
                best_travel = total_travel
                found_better_for_size = True
            elif len(meetings) == len(best_meetings) and len(meetings) > 0:
                if best_finish is None or finish_time < best_finish:
                    best_meetings = meetings
                    best_finish = finish_time
                    best_travel = total_travel
                    found_better_for_size = True
                elif finish_time == best_finish and total_travel < best_travel:
                    best_meetings = meetings
                    best_finish = finish_time
                    best_travel = total_travel
                    found_better_for_size = True
    # If we have found at least one feasible schedule for this size, no need to check smaller sizes
    if found_better_for_size and len(best_meetings) == r:
        break

output = {
    "itinerary": best_meetings
}

print(json.dumps(output, ensure_ascii=False, indent=2))