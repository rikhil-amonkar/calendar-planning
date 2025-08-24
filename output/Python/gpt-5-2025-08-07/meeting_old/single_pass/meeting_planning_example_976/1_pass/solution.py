import json
from functools import lru_cache

def time_to_minutes(t):
    # t like '9:00' or '13:30'
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (constraints)
start_location = "Embarcadero"
arrival_time_str = "9:00"

people = [
    {"name": "Matthew", "location": "Bayview", "start": "19:15", "end": "22:00", "min_duration": 120},
    {"name": "Karen", "location": "Chinatown", "start": "19:15", "end": "21:15", "min_duration": 90},
    {"name": "Sarah", "location": "Alamo Square", "start": "20:00", "end": "21:45", "min_duration": 105},
    {"name": "Jessica", "location": "Nob Hill", "start": "16:30", "end": "18:45", "min_duration": 120},
    {"name": "Stephanie", "location": "Presidio", "start": "7:30", "end": "10:15", "min_duration": 60},
    {"name": "Mary", "location": "Union Square", "start": "16:45", "end": "21:30", "min_duration": 60},
    {"name": "Charles", "location": "The Castro", "start": "16:30", "end": "22:00", "min_duration": 105},
    {"name": "Nancy", "location": "North Beach", "start": "14:45", "end": "20:00", "min_duration": 15},
    {"name": "Thomas", "location": "Fisherman's Wharf", "start": "13:30", "end": "19:00", "min_duration": 30},
    {"name": "Brian", "location": "Marina District", "start": "12:15", "end": "18:00", "min_duration": 60},
]

# Convert times to minutes
for p in people:
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

arrival_time = time_to_minutes(arrival_time_str)

# Travel times (in minutes), directed
TT = {
    "Embarcadero": {
        "Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20,
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6,
        "Marina District": 12
    },
    "Bayview": {
        "Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32,
        "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25,
        "Marina District": 27
    },
    "Chinatown": {
        "Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19,
        "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8,
        "Marina District": 12
    },
    "Alamo Square": {
        "Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17,
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19,
        "Marina District": 15
    },
    "Nob Hill": {
        "Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17,
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10,
        "Marina District": 11
    },
    "Presidio": {
        "Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18,
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Fisherman's Wharf": 19,
        "Marina District": 11
    },
    "Union Square": {
        "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9,
        "Presidio": 24, "The Castro": 17, "North Beach": 10, "Fisherman's Wharf": 15,
        "Marina District": 18
    },
    "The Castro": {
        "Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16,
        "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 24,
        "Marina District": 21
    },
    "North Beach": {
        "Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16, "Nob Hill": 7,
        "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5,
        "Marina District": 9
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11,
        "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 6,
        "Marina District": 9
    },
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12,
        "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11,
        "Fisherman's Wharf": 10
    }
}

# Sort people by window end to encourage earlier pruning
people_indices = list(range(len(people)))
people_sorted_by_end = sorted(people_indices, key=lambda i: people[i]["end_min"])

# Build a mapping from index to its order for consistent iteration
order_rank = {i: rank for rank, i in enumerate(people_sorted_by_end)}

@lru_cache(maxsize=None)
def search(current_location, current_time, visited_mask):
    best = (0, 0, ())  # (count, total_meeting_minutes, itinerary_tuple)
    # Iterate candidates ordered by earliest end to prune naturally
    candidates = [i for i in range(len(people)) if not (visited_mask & (1 << i))]
    candidates.sort(key=lambda i: people[i]["end_min"])
    for i in candidates:
        person = people[i]
        # Travel time
        if current_location not in TT or person["location"] not in TT[current_location]:
            continue  # if missing edge, skip
        travel = TT[current_location][person["location"]]
        arrival = current_time + travel
        start = max(arrival, person["start_min"])
        end = start + person["min_duration"]
        if end <= person["end_min"]:
            next_mask = visited_mask | (1 << i)
            tail = search(person["location"], end, next_mask)
            proposed_count = 1 + tail[0]
            proposed_minutes = person["min_duration"] + tail[1]
            proposed_itin = ((person["name"], person["location"], start, end),) + tail[2]
            # Tie-breakers: max count, then max total meeting minutes, then earliest final end time
            if proposed_count > best[0]:
                best = (proposed_count, proposed_minutes, proposed_itin)
            elif proposed_count == best[0]:
                if proposed_minutes > best[1]:
                    best = (proposed_count, proposed_minutes, proposed_itin)
                elif proposed_minutes == best[1]:
                    # Compare final end time (earlier finish is slightly preferred)
                    last_end_best = best[2][-1][3] if best[2] else float('inf')
                    last_end_prop = proposed_itin[-1][3] if proposed_itin else float('inf')
                    if last_end_prop < last_end_best:
                        best = (proposed_count, proposed_minutes, proposed_itin)
    return best

# Kick off search
best_count, best_minutes, best_itin = search(start_location, arrival_time, 0)

# Build JSON output
itinerary = []
for name, location, start, end in best_itin:
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": name,
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))