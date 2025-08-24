import json

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (directed, in minutes)
travel = {
    "Sunset District": {
        "Presidio": 16,
        "Nob Hill": 27,
        "Pacific Heights": 21,
        "Mission District": 25,
        "Marina District": 21,
        "North Beach": 28,
        "Russian Hill": 24,
        "Richmond District": 12,
        "Embarcadero": 30,
        "Alamo Square": 17,
        "Sunset District": 0
    },
    "Presidio": {
        "Sunset District": 15,
        "Nob Hill": 18,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Marina District": 11,
        "North Beach": 18,
        "Russian Hill": 14,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Alamo Square": 19
    },
    "Nob Hill": {
        "Sunset District": 24,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Mission District": 13,
        "Marina District": 11,
        "North Beach": 8,
        "Russian Hill": 5,
        "Richmond District": 14,
        "Embarcadero": 9,
        "Alamo Square": 11
    },
    "Pacific Heights": {
        "Sunset District": 21,
        "Presidio": 11,
        "Nob Hill": 8,
        "Mission District": 15,
        "Marina District": 6,
        "North Beach": 9,
        "Russian Hill": 7,
        "Richmond District": 12,
        "Embarcadero": 10,
        "Alamo Square": 10
    },
    "Mission District": {
        "Sunset District": 24,
        "Presidio": 25,
        "Nob Hill": 12,
        "Pacific Heights": 16,
        "Marina District": 19,
        "North Beach": 17,
        "Russian Hill": 15,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Alamo Square": 11
    },
    "Marina District": {
        "Sunset District": 19,
        "Presidio": 10,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Mission District": 20,
        "North Beach": 11,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Alamo Square": 15
    },
    "North Beach": {
        "Sunset District": 27,
        "Presidio": 17,
        "Nob Hill": 7,
        "Pacific Heights": 8,
        "Mission District": 18,
        "Marina District": 9,
        "Russian Hill": 4,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Alamo Square": 16
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Presidio": 14,
        "Nob Hill": 5,
        "Pacific Heights": 7,
        "Mission District": 16,
        "Marina District": 7,
        "North Beach": 5,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Alamo Square": 15
    },
    "Richmond District": {
        "Sunset District": 11,
        "Presidio": 7,
        "Nob Hill": 17,
        "Pacific Heights": 10,
        "Mission District": 20,
        "Marina District": 9,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19,
        "Alamo Square": 13
    },
    "Embarcadero": {
        "Sunset District": 30,
        "Presidio": 20,
        "Nob Hill": 10,
        "Pacific Heights": 11,
        "Mission District": 20,
        "Marina District": 12,
        "North Beach": 5,
        "Russian Hill": 8,
        "Richmond District": 21,
        "Alamo Square": 19
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Presidio": 17,
        "Nob Hill": 11,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Marina District": 15,
        "North Beach": 15,
        "Russian Hill": 13,
        "Richmond District": 11,
        "Embarcadero": 16
    }
}

# Friends and availability
def t(h, m): return h*60 + m

friends = [
    {"name": "Charles", "location": "Presidio", "start": t(13,15), "end": t(15,0), "duration": 105},
    {"name": "Robert", "location": "Nob Hill", "start": t(13,15), "end": t(17,30), "duration": 90},
    {"name": "Nancy", "location": "Pacific Heights", "start": t(14,45), "end": t(22,0), "duration": 105},
    {"name": "Brian", "location": "Mission District", "start": t(15,30), "end": t(22,0), "duration": 60},
    {"name": "Kimberly", "location": "Marina District", "start": t(17,0), "end": t(19,45), "duration": 75},
    {"name": "David", "location": "North Beach", "start": t(14,45), "end": t(16,30), "duration": 75},
    {"name": "William", "location": "Russian Hill", "start": t(12,30), "end": t(19,15), "duration": 120},
    {"name": "Jeffrey", "location": "Richmond District", "start": t(12,0), "end": t(19,15), "duration": 45},
    {"name": "Karen", "location": "Embarcadero", "start": t(14,15), "end": t(20,45), "duration": 60},
    {"name": "Joshua", "location": "Alamo Square", "start": t(18,45), "end": t(22,0), "duration": 60}
]

start_location = "Sunset District"
start_time = t(9,0)

# Precompute a quick feasibility check for pruning
def can_still_meet_from(time_now, f):
    latest_start = f["end"] - f["duration"]
    return time_now <= latest_start

best_global = {"count": 0}

def search(current_loc, current_time, visited_mask):
    # Base best is doing nothing more
    best_count = 0
    best_minutes = 0
    best_end_time = current_time
    best_itinerary = []

    # Compute an optimistic upper bound for pruning
    remaining_possible = 0
    for i, f in enumerate(friends):
        if not (visited_mask & (1 << i)):
            if can_still_meet_from(current_time, f):
                remaining_possible += 1
    if best_global["count"] >= best_count + remaining_possible:
        return best_count, best_minutes, best_end_time, best_itinerary

    for i, f in enumerate(friends):
        if visited_mask & (1 << i):
            continue
        # Check feasibility to meet friend f next
        if current_loc not in travel or f["location"] not in travel[current_loc]:
            continue
        arrival = current_time + travel[current_loc][f["location"]]
        start = max(arrival, f["start"])
        end = start + f["duration"]
        if end <= f["end"]:
            sub_count, sub_minutes, sub_end_time, sub_itin = search(
                f["location"], end, visited_mask | (1 << i)
            )
            total_count = 1 + sub_count
            total_minutes = f["duration"] + sub_minutes
            total_end_time = sub_end_time
            current_itinerary = [{
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": minutes_to_str(start),
                "end_time": minutes_to_str(end)
            }] + sub_itin

            # Update global best for pruning
            if total_count > best_global.get("count", 0):
                best_global["count"] = total_count

            # Choose best by count, then total minutes, then earlier end time
            better = False
            if total_count > best_count:
                better = True
            elif total_count == best_count:
                if total_minutes > best_minutes:
                    better = True
                elif total_minutes == best_minutes:
                    if total_end_time < best_end_time:
                        better = True
            if better:
                best_count = total_count
                best_minutes = total_minutes
                best_end_time = total_end_time
                best_itinerary = current_itinerary

    return best_count, best_minutes, best_end_time, best_itinerary

_, _, _, itinerary = search(start_location, start_time, 0)

output = {
    "itinerary": itinerary
}

print(json.dumps(output, ensure_ascii=False))