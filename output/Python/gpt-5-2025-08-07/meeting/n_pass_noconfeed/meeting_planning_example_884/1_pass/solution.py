# SOLUTION:
import json
import re
from functools import lru_cache

# Helper to parse times like '7:45AM', '5:30PM'
def parse_ampm(tstr):
    m = re.match(r'^\s*(\d{1,2}):(\d{2})\s*([AP]M)\s*$', tstr, re.IGNORECASE)
    if not m:
        raise ValueError(f"Invalid time format: {tstr}")
    h = int(m.group(1))
    mi = int(m.group(2))
    ampm = m.group(3).upper()
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + mi

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) between locations
travel_times = {
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,

    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 20,

    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,

    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,

    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,

    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 25,

    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Bayview"): 21,

    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,

    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Bayview"): 23,

    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Golden Gate Park"): 22,
}

def get_travel(a, b):
    if a == b:
        return 0
    return travel_times.get((a, b), travel_times.get((b, a)))

# Friends constraints
friends = [
    {"name": "Robert", "location": "Chinatown", "start": parse_ampm("7:45AM"), "end": parse_ampm("5:30PM"), "min": 120},
    {"name": "David", "location": "Sunset District", "start": parse_ampm("12:30PM"), "end": parse_ampm("7:45PM"), "min": 45},
    {"name": "Matthew", "location": "Alamo Square", "start": parse_ampm("8:45AM"), "end": parse_ampm("1:45PM"), "min": 90},
    {"name": "Jessica", "location": "Financial District", "start": parse_ampm("9:30AM"), "end": parse_ampm("6:45PM"), "min": 45},
    {"name": "Melissa", "location": "North Beach", "start": parse_ampm("7:15AM"), "end": parse_ampm("4:45PM"), "min": 45},
    {"name": "Mark", "location": "Embarcadero", "start": parse_ampm("3:15PM"), "end": parse_ampm("5:00PM"), "min": 45},
    {"name": "Deborah", "location": "Presidio", "start": parse_ampm("7:00PM"), "end": parse_ampm("7:45PM"), "min": 45},
    {"name": "Karen", "location": "Golden Gate Park", "start": parse_ampm("7:30PM"), "end": parse_ampm("10:00PM"), "min": 120},
    {"name": "Laura", "location": "Bayview", "start": parse_ampm("9:15PM"), "end": parse_ampm("10:15PM"), "min": 15},
]

friend_index = {f["name"]: i for i, f in enumerate(friends)}

def earliest_meeting(current_loc, current_time, f):
    travel = get_travel(current_loc, f["location"])
    if travel is None:
        return None
    arrival = current_time + travel
    start = max(arrival, f["start"])
    end = start + f["min"]
    if end <= f["end"]:
        wait = max(0, start - arrival)
        return {
            "person": f["name"],
            "location": f["location"],
            "start": start,
            "end": end,
            "travel": travel,
            "wait": wait
        }
    return None

# Search for optimal itinerary
start_location = "Richmond District"
start_time = parse_ampm("9:00AM")

best_solution = {
    "count": 0,
    "meetings": [],
    "final_end": start_time,
    "total_travel": 0,
    "total_wait": 0
}

@lru_cache(maxsize=None)
def upper_bound_from_state(current_time, remaining_mask):
    # A loose upper bound: count of remaining friends whose window end >= current_time
    # and min duration can still potentially fit if starting at current_time without travel.
    cnt = 0
    for i, f in enumerate(friends):
        if (remaining_mask >> i) & 1:
            # Assume zero travel and no waiting needed beyond current_time
            earliest_start = max(current_time, f["start"])
            if earliest_start + f["min"] <= f["end"]:
                cnt += 1
    return cnt

def better_schedule(a, b):
    # Returns True if a is better than b
    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    if a["final_end"] != b["final_end"]:
        return a["final_end"] < b["final_end"]
    if a["total_travel"] != b["total_travel"]:
        return a["total_travel"] < b["total_travel"]
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    return False

def search(current_loc, current_time, remaining_mask, meetings, total_travel, total_wait):
    global best_solution

    current_count = len(meetings)

    # Prune if even optimistically we can't beat the best
    optimistic = current_count + upper_bound_from_state(current_time, remaining_mask)
    if optimistic < best_solution["count"]:
        return

    # Gather feasible next candidates
    candidates = []
    for i, f in enumerate(friends):
        if (remaining_mask >> i) & 1:
            em = earliest_meeting(current_loc, current_time, f)
            if em is not None:
                em["idx"] = i
                candidates.append(em)

    # Update best if no more candidates
    if not candidates:
        sol = {
            "count": current_count,
            "meetings": meetings,
            "final_end": current_time,
            "total_travel": total_travel,
            "total_wait": total_wait
        }
        if better_schedule(sol, best_solution):
            best_solution = sol
        return

    # Sort candidates by their end time (earliest finishing first), then start time
    candidates.sort(key=lambda x: (x["end"], x["start"]))

    for em in candidates:
        i = em["idx"]
        new_meeting = {
            "action": "meet",
            "location": friends[i]["location"],
            "person": friends[i]["name"],
            "start_time": em["start"],
            "end_time": em["end"]
        }
        new_meetings = meetings + [new_meeting]
        new_mask = remaining_mask & ~(1 << i)
        search(
            friends[i]["location"],
            em["end"],
            new_mask,
            new_meetings,
            total_travel + em["travel"],
            total_wait + em["wait"]
        )

# Initialize remaining mask with all friends available
remaining_mask_init = (1 << len(friends)) - 1

# Kick off search
search(start_location, start_time, remaining_mask_init, [], 0, 0)

# Prepare JSON output
def to_json_itinerary(meetings):
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": fmt_time(m["start_time"]),
            "end_time": fmt_time(m["end_time"])
        })
    return {"itinerary": itinerary}

print(json.dumps(to_json_itinerary(best_solution["meetings"]), indent=2))