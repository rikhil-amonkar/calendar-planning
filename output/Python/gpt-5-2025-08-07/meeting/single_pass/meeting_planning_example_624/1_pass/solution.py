import json
from itertools import permutations

def parse_time(s):
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        h_m = s[:-2]
        h, m = map(int, h_m.split(":"))
        if ampm == "AM":
            if h == 12:
                h = 0
        else:  # PM
            if h != 12:
                h += 12
        return h * 60 + m
    else:
        h, m = map(int, s.split(":"))
        return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
day_start_location = "Golden Gate Park"
day_start_time = parse_time("9:00AM")

# Travel times (in minutes)
travel = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Chinatown": 23,
        "Alamo Square": 10,
        "North Beach": 24,
        "Russian Hill": 19,
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "The Castro": 6,
        "Chinatown": 19,
        "Alamo Square": 5,
        "North Beach": 19,
        "Russian Hill": 17,
    },
    "Fisherman's Wharf": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 22,
        "The Castro": 26,
        "Chinatown": 12,
        "Alamo Square": 20,
        "North Beach": 6,
        "Russian Hill": 7,
    },
    "The Castro": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 6,
        "Fisherman's Wharf": 24,
        "Chinatown": 20,
        "Alamo Square": 8,
        "North Beach": 20,
        "Russian Hill": 18,
    },
    "Chinatown": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 8,
        "The Castro": 22,
        "Alamo Square": 17,
        "North Beach": 3,
        "Russian Hill": 7,
    },
    "Alamo Square": {
        "Golden Gate Park": 9,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Chinatown": 16,
        "North Beach": 15,
        "Russian Hill": 13,
    },
    "North Beach": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Russian Hill": 4,
    },
    "Russian Hill": {
        "Golden Gate Park": 21,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Chinatown": 9,
        "Alamo Square": 15,
        "North Beach": 5,
    },
}

# Friends constraints
friends = [
    {
        "name": "Carol",
        "location": "Haight-Ashbury",
        "window_start": parse_time("9:30PM"),
        "window_end": parse_time("10:30PM"),
        "min_duration": 60,
    },
    {
        "name": "Laura",
        "location": "Fisherman's Wharf",
        "window_start": parse_time("11:45AM"),
        "window_end": parse_time("9:30PM"),
        "min_duration": 60,
    },
    {
        "name": "Karen",
        "location": "The Castro",
        "window_start": parse_time("7:15AM"),
        "window_end": parse_time("2:00PM"),
        "min_duration": 75,
    },
    {
        "name": "Elizabeth",
        "location": "Chinatown",
        "window_start": parse_time("12:15PM"),
        "window_end": parse_time("9:30PM"),
        "min_duration": 75,
    },
    {
        "name": "Deborah",
        "location": "Alamo Square",
        "window_start": parse_time("12:00PM"),
        "window_end": parse_time("3:00PM"),
        "min_duration": 105,
    },
    {
        "name": "Jason",
        "location": "North Beach",
        "window_start": parse_time("2:45PM"),
        "window_end": parse_time("7:00PM"),
        "min_duration": 90,
    },
    {
        "name": "Steven",
        "location": "Russian Hill",
        "window_start": parse_time("2:45PM"),
        "window_end": parse_time("6:30PM"),
        "min_duration": 120,
    },
]

# Backtracking search to maximize number of friends met
best_solution = {
    "schedule": [],
    "end_time": day_start_time,
    "meeting_time_sum": 0,
    "metric": (float("inf"), float("inf"), float("inf")),  # placeholder for comparison
}

def compute_metric(schedule, end_time, meeting_time_sum):
    count = len(schedule)
    non_meeting_time = end_time - day_start_time - meeting_time_sum
    # We want to maximize count, then minimize non_meeting_time, then minimize end_time
    # For tuple minimization, use (-count, non_meeting_time, end_time)
    return (-count, non_meeting_time, end_time)

def update_best(schedule, end_time, meeting_time_sum):
    global best_solution
    metric = compute_metric(schedule, end_time, meeting_time_sum)
    if metric < best_solution["metric"]:
        best_solution = {
            "schedule": list(schedule),
            "end_time": end_time,
            "meeting_time_sum": meeting_time_sum,
            "metric": metric,
        }

# Optional heuristic: sort friends by window end to encourage feasibility
friends_sorted = sorted(friends, key=lambda f: f["window_end"])

def search(current_loc, current_time, remaining, schedule, meeting_time_sum):
    # Update best at every node (even if we stop here)
    update_best(schedule, current_time, meeting_time_sum)

    # Prune if we cannot beat best count even by visiting all remaining
    current_best_count = -best_solution["metric"][0]
    if len(schedule) + len(remaining) < current_best_count:
        return

    for i, f in enumerate(remaining):
        # Travel time
        if current_loc not in travel or f["location"] not in travel[current_loc]:
            continue
        t_travel = travel[current_loc][f["location"]]
        arrival = current_time + t_travel
        start = max(arrival, f["window_start"])
        end = start + f["min_duration"]
        if end <= f["window_end"]:
            # Feasible to meet f next
            schedule_next = schedule + [{
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": start,
                "end_time": end
            }]
            remaining_next = remaining[:i] + remaining[i+1:]
            search(f["location"], end, remaining_next, schedule_next, meeting_time_sum + f["min_duration"])

# Start search
search(day_start_location, day_start_time, friends_sorted, [], 0)

# Build output in required JSON format with times formatted
itinerary = []
for m in best_solution["schedule"]:
    itinerary.append({
        "action": m["action"],
        "location": m["location"],
        "person": m["person"],
        "start_time": fmt_time(m["start_time"]),
        "end_time": fmt_time(m["end_time"]),
    })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))