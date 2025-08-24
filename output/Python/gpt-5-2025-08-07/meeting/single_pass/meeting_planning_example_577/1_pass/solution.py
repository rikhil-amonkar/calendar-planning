import json
from copy import deepcopy

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input data
start_location = "Haight-Ashbury"
start_time_str = "9:00"

dist = {
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
        "person": "Stephanie",
        "location": "Russian Hill",
        "window_start": "20:00",
        "window_end": "20:45",
        "min_duration": 15
    },
    {
        "person": "Kevin",
        "location": "Fisherman's Wharf",
        "window_start": "19:15",
        "window_end": "21:45",
        "min_duration": 75
    },
    {
        "person": "Robert",
        "location": "Nob Hill",
        "window_start": "7:45",
        "window_end": "10:30",
        "min_duration": 90
    },
    {
        "person": "Steven",
        "location": "Golden Gate Park",
        "window_start": "8:30",
        "window_end": "17:00",
        "min_duration": 75
    },
    {
        "person": "Anthony",
        "location": "Alamo Square",
        "window_start": "7:45",
        "window_end": "19:45",
        "min_duration": 15
    },
    {
        "person": "Sandra",
        "location": "Pacific Heights",
        "window_start": "14:45",
        "window_end": "21:45",
        "min_duration": 45
    }
]

# Convert times to minutes
for p in people:
    p["ws"] = time_to_minutes(p["window_start"])
    p["we"] = time_to_minutes(p["window_end"])

start_time = time_to_minutes(start_time_str)

# Build index for people
name_to_index = {p["person"]: i for i, p in enumerate(people)}

def feasible_meeting(cur_loc, cur_time, person):
    travel = dist[cur_loc][person["location"]]
    arrival = cur_time + travel
    start = max(arrival, person["ws"])
    end = start + person["min_duration"]
    if end <= person["we"]:
        return start, end, travel
    return None

best_solution = {
    "count": 0,
    "end_time": float('inf'),
    "travel": float('inf'),
    "itinerary": []
}

def search(cur_loc, cur_time, visited, itinerary, travel_sum):
    global best_solution

    # Evaluate current solution
    count = len(itinerary)
    last_end = cur_time
    # Update best solution if better
    update = False
    if count > best_solution["count"]:
        update = True
    elif count == best_solution["count"]:
        if last_end < best_solution["end_time"]:
            update = True
        elif last_end == best_solution["end_time"] and travel_sum < best_solution["travel"]:
            update = True
    if update:
        best_solution = {
            "count": count,
            "end_time": last_end,
            "travel": travel_sum,
            "itinerary": deepcopy(itinerary)
        }

    # Try to add another meeting
    # Order candidates by earliest feasible start to guide search
    candidates = []
    for p in people:
        if p["person"] in visited:
            continue
        feas = feasible_meeting(cur_loc, cur_time, p)
        if feas:
            start, end, travel = feas
            candidates.append((start, end, travel, p))
    candidates.sort(key=lambda x: (x[0], x[1]))  # earliest start first

    for start, end, travel, p in candidates:
        visited.add(p["person"])
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["person"],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        search(p["location"], end, visited, itinerary, travel_sum + travel)
        itinerary.pop()
        visited.remove(p["person"])

# Run search
search(start_location, start_time, set(), [], 0)

# Build output JSON
output = {
    "itinerary": best_solution["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))