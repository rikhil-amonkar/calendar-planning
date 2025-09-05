import json
from functools import lru_cache

def hm(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) between locations (directed, as given)
T = {
    "Mission District": {
        "The Castro": 7,
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20,
    },
    "The Castro": {
        "Mission District": 7,
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16,
    },
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14,
    },
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7,
    },
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11,
    },
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12,
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7,
    },
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Richmond District": 20,
    },
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20,
    },
}

# Participant availability and required minimums
people = [
    {"name": "Lisa", "location": "The Castro", "start": hm(19, 15), "end": hm(21, 15), "min": 120},
    {"name": "Daniel", "location": "Nob Hill", "start": hm(8, 15), "end": hm(11, 0), "min": 15},
    {"name": "Elizabeth", "location": "Presidio", "start": hm(21, 15), "end": hm(22, 15), "min": 45},
    {"name": "Steven", "location": "Marina District", "start": hm(16, 30), "end": hm(20, 45), "min": 90},
    {"name": "Timothy", "location": "Pacific Heights", "start": hm(12, 0), "end": hm(18, 0), "min": 90},
    {"name": "Ashley", "location": "Golden Gate Park", "start": hm(20, 45), "end": hm(21, 45), "min": 60},
    {"name": "Kevin", "location": "Chinatown", "start": hm(12, 0), "end": hm(19, 0), "min": 30},
    {"name": "Betty", "location": "Richmond District", "start": hm(13, 15), "end": hm(15, 45), "min": 30},
]

# Map name to person details for quick lookup
people_by_name = {p["name"]: p for p in people}
all_names = tuple(sorted(people_by_name.keys()))

start_location = "Mission District"
start_time = hm(9, 0)

# Precompute a list for iteration order heuristics (earlier window ends first)
people_sorted_by_end = sorted(people, key=lambda x: (x["end"], x["start"], x["min"]))
sorted_names = tuple(p["name"] for p in people_sorted_by_end)

@lru_cache(maxsize=None)
def search(current_loc, current_time, remaining_names):
    # remaining_names is a tuple of sorted names
    best = {
        "count": 0,
        "total_minutes": 0,
        "itinerary": [],
    }

    remaining = list(remaining_names)

    # Try each possible next person
    for name in remaining:
        person = people_by_name[name]
        loc = person["location"]
        avail_start = person["start"]
        avail_end = person["end"]
        min_dur = person["min"]

        # Travel time
        if current_loc not in T or loc not in T[current_loc]:
            continue  # If no travel time defined (shouldn't happen with provided data)
        travel = T[current_loc][loc]

        arrival_time = current_time + travel
        start_meet = max(arrival_time, avail_start)
        end_meet = start_meet + min_dur

        # Feasibility check
        if end_meet > avail_end:
            continue

        # Proceed recursively
        next_remaining = tuple(n for n in remaining if n != name)
        res = search(loc, end_meet, next_remaining)

        # Build current itinerary
        current_itinerary = [{
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_str(start_meet),
            "end_time": minutes_to_str(end_meet),
            "duration": min_dur,
        }] + res["itinerary"]

        count = 1 + res["count"]
        total_minutes = min_dur + res["total_minutes"]

        # Choose better result: maximize count, then total meeting minutes, then earliest finish time
        better = False
        if count > best["count"]:
            better = True
        elif count == best["count"]:
            if total_minutes > best["total_minutes"]:
                better = True
            elif total_minutes == best["total_minutes"]:
                # Tie-breaker: earliest final end time
                this_end_time = end_meet if not res["itinerary"] else hm(*map(int, res["itinerary"][-1]["end_time"].split(":")))
                best_end_time = None
                if best["itinerary"]:
                    best_end_time = hm(*map(int, best["itinerary"][-1]["end_time"].split(":")))
                else:
                    best_end_time = -1
                if this_end_time < best_end_time or best_end_time == -1:
                    better = True

        if better:
            best = {
                "count": count,
                "total_minutes": total_minutes,
                "itinerary": current_itinerary,
            }

    return best

# Start search
result = search(start_location, start_time, tuple(sorted(all_names)))

# The itinerary returned is constructed in forward order by our recursion
# Ensure it's sorted by actual meeting start times in case of ties
result_itinerary = result["itinerary"]
result_itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

# Strip duration from output per required schema
final_itinerary = []
for item in result_itinerary:
    final_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": item["start_time"],
        "end_time": item["end_time"],
    })

output = {"itinerary": final_itinerary}
print(json.dumps(output, ensure_ascii=False))