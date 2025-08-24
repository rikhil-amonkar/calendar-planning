import json
from functools import lru_cache

# Time helpers
def to_min(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Distances (directed, in minutes)
dist = {
    "Russian Hill": {
        "Marina District": 7,
        "Financial District": 11,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "The Castro": 21,
        "Bayview": 23,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Nob Hill": 5,
    },
    "Marina District": {
        "Russian Hill": 8,
        "Financial District": 17,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Sunset District": 19,
        "Haight-Ashbury": 16,
        "Nob Hill": 12,
    },
    "Financial District": {
        "Russian Hill": 11,
        "Marina District": 15,
        "Alamo Square": 17,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Nob Hill": 8,
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Marina District": 15,
        "Financial District": 17,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Sunset District": 16,
        "Haight-Ashbury": 5,
        "Nob Hill": 11,
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Marina District": 16,
        "Financial District": 26,
        "Alamo Square": 9,
        "The Castro": 13,
        "Bayview": 23,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Nob Hill": 20,
    },
    "The Castro": {
        "Russian Hill": 18,
        "Marina District": 21,
        "Financial District": 21,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Nob Hill": 16,
    },
    "Bayview": {
        "Russian Hill": 23,
        "Marina District": 27,
        "Financial District": 19,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Sunset District": 23,
        "Haight-Ashbury": 19,
        "Nob Hill": 20,
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Marina District": 21,
        "Financial District": 30,
        "Alamo Square": 17,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Nob Hill": 27,
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Marina District": 17,
        "Financial District": 21,
        "Alamo Square": 5,
        "Golden Gate Park": 7,
        "The Castro": 6,
        "Bayview": 18,
        "Sunset District": 15,
        "Nob Hill": 15,
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Marina District": 11,
        "Financial District": 9,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
        "The Castro": 17,
        "Bayview": 19,
        "Sunset District": 24,
        "Haight-Ashbury": 13,
    },
}

# Participants and constraints
participants = [
    {
        "name": "Mark",
        "location": "Marina District",
        "window_start": to_min(18, 45),
        "window_end": to_min(21, 0),
        "min_duration": 90,
    },
    {
        "name": "Karen",
        "location": "Financial District",
        "window_start": to_min(9, 30),
        "window_end": to_min(12, 45),
        "min_duration": 90,
    },
    {
        "name": "Barbara",
        "location": "Alamo Square",
        "window_start": to_min(10, 0),
        "window_end": to_min(19, 30),
        "min_duration": 90,
    },
    {
        "name": "Nancy",
        "location": "Golden Gate Park",
        "window_start": to_min(16, 45),
        "window_end": to_min(20, 0),
        "min_duration": 105,
    },
    {
        "name": "David",
        "location": "The Castro",
        "window_start": to_min(9, 0),
        "window_end": to_min(18, 0),
        "min_duration": 120,
    },
    {
        "name": "Linda",
        "location": "Bayview",
        "window_start": to_min(18, 15),
        "window_end": to_min(19, 45),
        "min_duration": 45,
    },
    {
        "name": "Kevin",
        "location": "Sunset District",
        "window_start": to_min(10, 0),
        "window_end": to_min(17, 45),
        "min_duration": 120,
    },
    {
        "name": "Matthew",
        "location": "Haight-Ashbury",
        "window_start": to_min(10, 15),
        "window_end": to_min(15, 30),
        "min_duration": 45,
    },
    {
        "name": "Andrew",
        "location": "Nob Hill",
        "window_start": to_min(11, 45),
        "window_end": to_min(16, 45),
        "min_duration": 105,
    },
]

# Start conditions
start_location = "Russian Hill"
start_time = to_min(9, 0)

# Pre-calc: order participants by increasing window_end to help pruning/ordering
indices_by_earliest_end = sorted(range(len(participants)), key=lambda i: participants[i]["window_end"])

# Global for pruning
best_global = {"count": 0}

def feasible_from_state(curr_loc, curr_time, unvisited_mask):
    # Upper bound on how many more people can be met from this state (naive feasibility)
    count = 0
    for i in range(len(participants)):
        if not (unvisited_mask & (1 << i)):
            continue
        p = participants[i]
        travel = dist[curr_loc][p["location"]]
        arrival = curr_time + travel
        start = max(arrival, p["window_start"])
        end = start + p["min_duration"]
        if end <= p["window_end"]:
            count += 1
    return count

@lru_cache(maxsize=None)
def search(curr_loc, curr_time, visited_mask):
    # Compute mask of unvisited
    total_people = len(participants)
    unvisited_mask = ((1 << total_people) - 1) ^ visited_mask

    # Base metrics: doing nothing more
    best_metrics = (0, 0, 0, 0, -curr_time)  # (count, total_meet_minutes, -travel_minutes, -wait_minutes, -final_end_time)
    best_itinerary = []

    # Branch and bound based on global best
    remaining_possible = feasible_from_state(curr_loc, curr_time, unvisited_mask)
    if remaining_possible == 0:
        return best_metrics, best_itinerary

    # Try each unvisited participant (ordered by heuristic)
    for i in indices_by_earliest_end:
        if not (unvisited_mask & (1 << i)):
            continue
        p = participants[i]
        travel = dist[curr_loc][p["location"]]
        arrival = curr_time + travel
        start = max(arrival, p["window_start"])
        end = start + p["min_duration"]
        if end > p["window_end"]:
            continue  # infeasible

        wait = max(0, p["window_start"] - arrival)

        next_metrics, next_itin = search(p["location"], end, visited_mask | (1 << i))

        # Combine metrics
        count = 1 + next_metrics[0]
        total_meet = p["min_duration"] + next_metrics[1]
        travel_used = travel + (-next_metrics[2])  # since stored as negative
        wait_used = wait + (-next_metrics[3])
        # Final end time is from next state; if no further meetings, it's end
        final_end_time = -next_metrics[4] if next_itin else end

        metrics = (
            count,
            total_meet,
            -travel_used,
            -wait_used,
            -final_end_time,
        )

        # Choose better based on lexicographic comparison
        if metrics > best_metrics:
            best_metrics = metrics
            best_itinerary = [{
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start": start,
                "end": end,
                "travel": travel,
                "wait": wait,
            }] + next_itin

            # Update global best for pruning in callers
            if count > best_global.get("count", 0):
                best_global["count"] = count

    return best_metrics, best_itinerary

# Run search
best_metrics, best_itinerary = search(start_location, start_time, 0)

# Build JSON itinerary with formatted times
output_itin = []
for item in best_itinerary:
    output_itin.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start"]),
        "end_time": fmt_time(item["end"]),
    })

result = {
    "itinerary": output_itin
}

print(json.dumps(result, ensure_ascii=False))