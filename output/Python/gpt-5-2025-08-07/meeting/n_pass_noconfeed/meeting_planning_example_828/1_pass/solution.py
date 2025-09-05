# SOLUTION:
import json

def time_to_minutes(t):
    # t like '9:00' or '13:30'
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (directed, in minutes)
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
        "Presidio": 10
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
        "Presidio": 7
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
        "Presidio": 24
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
        "Presidio": 17
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
        "Presidio": 17
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
        "Presidio": 11
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
        "Presidio": 20
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
        "Presidio": 22
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
        "Presidio": 17
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
        "North Beach": 18
    }
}

# People constraints
people = {
    "Stephanie": {
        "location": "Richmond District",
        "start": time_to_minutes("16:15"),
        "end": time_to_minutes("21:30"),
        "duration": 75
    },
    "William": {
        "location": "Union Square",
        "start": time_to_minutes("10:45"),
        "end": time_to_minutes("17:30"),
        "duration": 45
    },
    "Elizabeth": {
        "location": "Nob Hill",
        "start": time_to_minutes("12:15"),
        "end": time_to_minutes("15:00"),
        "duration": 105
    },
    "Joseph": {
        "location": "Fisherman's Wharf",
        "start": time_to_minutes("12:45"),
        "end": time_to_minutes("14:00"),
        "duration": 75
    },
    "Anthony": {
        "location": "Golden Gate Park",
        "start": time_to_minutes("13:00"),
        "end": time_to_minutes("20:30"),
        "duration": 75
    },
    "Barbara": {
        "location": "Embarcadero",
        "start": time_to_minutes("19:15"),
        "end": time_to_minutes("20:30"),
        "duration": 75
    },
    "Carol": {
        "location": "Financial District",
        "start": time_to_minutes("11:45"),
        "end": time_to_minutes("16:15"),
        "duration": 60
    },
    "Sandra": {
        "location": "North Beach",
        "start": time_to_minutes("10:00"),
        "end": time_to_minutes("12:30"),
        "duration": 15
    },
    "Kenneth": {
        "location": "Presidio",
        "start": time_to_minutes("21:15"),
        "end": time_to_minutes("22:15"),
        "duration": 45
    }
}

start_location = "Marina District"
start_time = time_to_minutes("9:00")

def feasible_meeting(curr_loc, curr_time, person):
    loc = person["location"]
    if curr_loc not in travel or loc not in travel[curr_loc]:
        return None
    t_travel = travel[curr_loc][loc]
    arrival = curr_time + t_travel
    start = max(arrival, person["start"])
    end = start + person["duration"]
    if end <= person["end"]:
        wait = start - arrival
        return start, end, wait, t_travel
    return None

def better_score(a, b):
    # Compare schedules by:
    # 1) max number met
    # 2) earliest last end time
    # 3) minimal total waiting
    # 4) minimal total travel
    ta = (a["count"], -a["last_end"], -a["wait"], -a["travel"])
    tb = (b["count"], -b["last_end"], -b["wait"], -b["travel"])
    return ta > tb

def dfs(curr_loc, curr_time, remaining_names):
    best = {
        "itinerary": [],
        "count": 0,
        "last_end": curr_time,
        "wait": 0,
        "travel": 0
    }
    # Deterministic iteration for reproducibility
    for name in sorted(remaining_names):
        res = feasible_meeting(curr_loc, curr_time, people[name])
        if not res:
            continue
        start, end, wait, t_travel = res
        child = dfs(people[name]["location"], end, remaining_names - {name})
        itinerary = [{
            "action": "meet",
            "location": people[name]["location"],
            "person": name,
            "start": start,
            "end": end
        }] + child["itinerary"]
        candidate = {
            "itinerary": itinerary,
            "count": 1 + child["count"],
            "last_end": child["last_end"] if child["count"] > 0 else end,
            "wait": wait + child["wait"],
            "travel": t_travel + child["travel"]
        }
        if better_score(candidate, best):
            best = candidate
    return best

def build_output():
    result = dfs(start_location, start_time, set(people.keys()))
    output_itinerary = []
    for item in result["itinerary"]:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_time(item["start"]),
            "end_time": minutes_to_time(item["end"])
        })
    return {"itinerary": output_itinerary}

if __name__ == "__main__":
    schedule = build_output()
    print(json.dumps(schedule, indent=2))