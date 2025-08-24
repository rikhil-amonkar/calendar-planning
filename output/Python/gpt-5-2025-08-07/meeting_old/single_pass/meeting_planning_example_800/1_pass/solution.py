import json

def parse_time(s):
    # s like '9:00' or '15:30', 24-hour with possible no leading zero
    h, m = s.split(':')
    return int(h) * 60 + int(m)

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
travel = {
    "Union Square": {
        "The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15,
        "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14, "Haight-Ashbury": 18
    },
    "The Castro": {
        "Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8,
        "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7, "Haight-Ashbury": 6
    },
    "North Beach": {
        "Union Square": 7, "The Castro": 23, "Embarcadero": 6, "Alamo Square": 16,
        "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18, "Haight-Ashbury": 18
    },
    "Embarcadero": {
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Alamo Square": 19,
        "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20, "Haight-Ashbury": 21
    },
    "Alamo Square": {
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16,
        "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10, "Haight-Ashbury": 5
    },
    "Nob Hill": {
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9,
        "Alamo Square": 11, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13, "Haight-Ashbury": 13
    },
    "Presidio": {
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20,
        "Alamo Square": 19, "Nob Hill": 18, "Fisherman's Wharf": 19, "Mission District": 26, "Haight-Ashbury": 15
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8,
        "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Mission District": 22, "Haight-Ashbury": 22
    },
    "Mission District": {
        "Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19,
        "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22, "Haight-Ashbury": 12
    },
    "Haight-Ashbury": {
        "Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20,
        "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23, "Mission District": 11
    }
}

# Friends constraints
friends = {
    "Melissa": {"location": "The Castro", "start": "20:15", "end": "21:15", "min_minutes": 30},
    "Kimberly": {"location": "North Beach", "start": "7:00", "end": "10:30", "min_minutes": 15},
    "Joseph": {"location": "Embarcadero", "start": "15:30", "end": "19:30", "min_minutes": 75},
    "Barbara": {"location": "Alamo Square", "start": "20:45", "end": "21:45", "min_minutes": 15},
    "Kenneth": {"location": "Nob Hill", "start": "12:15", "end": "17:15", "min_minutes": 105},
    "Joshua": {"location": "Presidio", "start": "16:30", "end": "18:15", "min_minutes": 105},
    "Brian": {"location": "Fisherman's Wharf", "start": "9:30", "end": "15:30", "min_minutes": 45},
    "Steven": {"location": "Mission District", "start": "19:30", "end": "21:00", "min_minutes": 90},
    "Betty": {"location": "Haight-Ashbury", "start": "19:00", "end": "20:30", "min_minutes": 90}
}

# Convert times to minutes
for person, info in friends.items():
    info["start_min"] = parse_time(info["start"])
    info["end_min"] = parse_time(info["end"])

start_location = "Union Square"
start_time = parse_time("9:00")

people = list(friends.keys())

# Order friends by window end, then start, then duration descending to improve pruning
people_sorted = sorted(people, key=lambda p: (friends[p]["end_min"], friends[p]["start_min"], -friends[p]["min_minutes"]))

from functools import lru_cache

def feasible_meeting(current_loc, current_time, person):
    info = friends[person]
    loc = info["location"]
    travel_time = travel[current_loc][loc]
    arrival = current_time + travel_time
    latest_start = info["end_min"] - info["min_minutes"]
    if arrival > latest_start:
        return []  # infeasible
    earliest_start = max(arrival, info["start_min"])
    candidates = sorted(set([earliest_start, latest_start]))
    meetings = []
    for s in candidates:
        if s < earliest_start or s > latest_start:
            continue
        meetings.append((s, s + info["min_minutes"]))
    return meetings

@lru_cache(maxsize=None)
def best_from_state(current_loc, current_time, remaining_tuple):
    remaining = list(remaining_tuple)
    best = {
        "count": 0,
        "finish": current_time,
        "schedule": []
    }
    # Upper bound pruning: remaining count + current_count
    # Try each friend as next
    for person in remaining:
        for s, e in feasible_meeting(current_loc, current_time, person):
            info = friends[person]
            loc = info["location"]
            new_remaining = tuple(x for x in remaining if x != person)
            tail = best_from_state(loc, e, new_remaining)
            total_count = 1 + tail["count"]
            finish_time = tail["finish"] if tail["schedule"] else e
            # Compute final finish as end of last meeting in combined schedule
            if tail["schedule"]:
                finish_time = tail["finish"]
            else:
                finish_time = e
            proposed_schedule = [{"action": "meet", "location": loc, "person": person, "start": s, "end": e}] + tail["schedule"]
            # Choose better by count, then earlier finish, then shorter total day span
            better = False
            if total_count > best["count"]:
                better = True
            elif total_count == best["count"]:
                # Earlier finish preferred
                if (tail["finish"] if tail["schedule"] else e) < best["finish"]:
                    better = True
                elif (tail["finish"] if tail["schedule"] else e) == best["finish"]:
                    # As secondary tiebreaker, minimize start-to-finish span
                    span_prop = proposed_schedule[-1]["end"] - proposed_schedule[0]["start"]
                    if best["schedule"]:
                        span_best = best["schedule"][-1]["end"] - best["schedule"][0]["start"]
                    else:
                        span_best = 0
                    if span_prop < span_best:
                        better = True
            if better:
                best = {
                    "count": total_count,
                    "finish": (tail["finish"] if tail["schedule"] else e),
                    "schedule": proposed_schedule
                }
    return best

result = best_from_state(start_location, start_time, tuple(people_sorted))

# Convert schedule to required output format and times
itinerary = []
for item in result["schedule"]:
    itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start"]),
        "end_time": fmt_time(item["end"])
    })

output = {"itinerary": itinerary}

print(json.dumps(output, ensure_ascii=False))