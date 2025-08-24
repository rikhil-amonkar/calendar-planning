import json

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) directional matrix
travel = {
    "Marina District": {
        "Richmond District": 11,
        "Union Square": 16,
        "Nob Hill": 12,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Financial District": 17,
        "North Beach": 11,
        "Presidio": 10,
    },
    "Richmond District": {
        "Marina District": 9,
        "Union Square": 21,
        "Nob Hill": 17,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "North Beach": 17,
        "Presidio": 7,
    },
    "Union Square": {
        "Marina District": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Fisherman's Wharf": 15,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Financial District": 9,
        "North Beach": 10,
        "Presidio": 24,
    },
    "Nob Hill": {
        "Marina District": 11,
        "Richmond District": 14,
        "Union Square": 7,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Financial District": 9,
        "North Beach": 8,
        "Presidio": 17,
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Financial District": 11,
        "North Beach": 6,
        "Presidio": 17,
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 20,
        "Fisherman's Wharf": 24,
        "Embarcadero": 25,
        "Financial District": 26,
        "North Beach": 23,
        "Presidio": 11,
    },
    "Embarcadero": {
        "Marina District": 12,
        "Richmond District": 21,
        "Union Square": 10,
        "Nob Hill": 10,
        "Fisherman's Wharf": 6,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20,
    },
    "Financial District": {
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Nob Hill": 8,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "North Beach": 7,
        "Presidio": 22,
    },
    "North Beach": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 7,
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Financial District": 8,
        "Presidio": 17,
    },
    "Presidio": {
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Financial District": 23,
        "North Beach": 18,
    },
}

# People constraints
people = [
    {"name": "Stephanie", "location": "Richmond District", "start": to_minutes("16:15"), "end": to_minutes("21:30"), "min": 75},
    {"name": "William", "location": "Union Square", "start": to_minutes("10:45"), "end": to_minutes("17:30"), "min": 45},
    {"name": "Elizabeth", "location": "Nob Hill", "start": to_minutes("12:15"), "end": to_minutes("15:00"), "min": 105},
    {"name": "Joseph", "location": "Fisherman's Wharf", "start": to_minutes("12:45"), "end": to_minutes("14:00"), "min": 75},
    {"name": "Anthony", "location": "Golden Gate Park", "start": to_minutes("13:00"), "end": to_minutes("20:30"), "min": 75},
    {"name": "Barbara", "location": "Embarcadero", "start": to_minutes("19:15"), "end": to_minutes("20:30"), "min": 75},
    {"name": "Carol", "location": "Financial District", "start": to_minutes("11:45"), "end": to_minutes("16:15"), "min": 60},
    {"name": "Sandra", "location": "North Beach", "start": to_minutes("10:00"), "end": to_minutes("12:30"), "min": 15},
    {"name": "Kenneth", "location": "Presidio", "start": to_minutes("21:15"), "end": to_minutes("22:15"), "min": 45},
]

# Index people for set operations
for i, p in enumerate(people):
    p["id"] = i

start_location = "Marina District"
start_time = to_minutes("9:00")

from functools import lru_cache

# Precompute window lengths
for p in people:
    p["window_len"] = p["end"] - p["start"]

# Convert id -> person dict for quick lookup
people_by_id = {p["id"]: p for p in people}

# For convenience, list of ids
all_ids = tuple(p["id"] for p in people)

def feasible_meeting(curr_loc, curr_time, person):
    # Returns (start, end, travel_time) if feasible, else None
    t_travel = travel[curr_loc][person["location"]]
    arrive = curr_time + t_travel
    start = max(arrive, person["start"])
    end = start + person["min"]
    if end <= person["end"]:
        return start, end, t_travel
    return None

@lru_cache(maxsize=None)
def search(curr_loc, curr_time, remaining_ids):
    # remaining_ids is a tuple of ints (ids), sorted
    # Returns (count, total_meeting_minutes, -final_end_time, total_travel_minutes, schedule_list)
    best = (0, 0, -curr_time, 0, [])  # no more meetings from here
    for idx, pid in enumerate(remaining_ids):
        person = people_by_id[pid]
        feas = feasible_meeting(curr_loc, curr_time, person)
        if feas is None:
            continue
        start, end, t_travel = feas
        # Next state
        new_remaining = list(remaining_ids)
        new_remaining.pop(idx)
        new_remaining = tuple(new_remaining)
        sub = search(person["location"], end, new_remaining)
        # final end time of the chain
        sub_count, sub_minutes, sub_neg_final_end, sub_travel, sub_sched = sub
        # If sub schedule empty, final end is end; else computed in sub_neg_final_end already
        if sub_count == 0:
            neg_final_end = -end
        else:
            neg_final_end = sub_neg_final_end
        cand = (
            1 + sub_count,
            person["min"] + sub_minutes,
            neg_final_end,
            t_travel + sub_travel,
            [{"action": "meet", "location": person["location"], "person": person["name"], "start": start, "end": end}] + sub_sched,
        )
        # Compare candidates: maximize count, then total meeting minutes, then earlier final end (i.e., more negative), then minimize total travel
        if (
            cand[0] > best[0]
            or (cand[0] == best[0] and cand[1] > best[1])
            or (cand[0] == best[0] and cand[1] == best[1] and cand[2] > best[2])  # more negative => earlier final end
            or (cand[0] == best[0] and cand[1] == best[1] and cand[2] == best[2] and cand[3] < best[3])
        ):
            best = cand
    return best

best_result = search(start_location, start_time, tuple(all_ids))
best_schedule = best_result[4]

# Build JSON itinerary
output = {"itinerary": []}
for entry in best_schedule:
    output["itinerary"].append({
        "action": "meet",
        "location": entry["location"],
        "person": entry["person"],
        "start_time": to_time_str(entry["start"]),
        "end_time": to_time_str(entry["end"]),
    })

print(json.dumps(output))