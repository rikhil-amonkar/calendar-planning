#!/usr/bin/env python3
import json
import itertools

# Helper functions for time conversion
def time_to_minutes(t):
    # t in "H:MM" format (e.g., "9:00", "21:15")
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times as provided (in minutes)
travel_times = {
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,
    
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 26,
    
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,
    
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,
    
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Bayview"): 19,
    
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
}

# Define friends meeting constraints and info.
# Time strings are in 24-hour format.
friends = {
    "Kenneth": {
        "location": "Richmond District",
        "avail_start": time_to_minutes("21:15"),
        "avail_end": time_to_minutes("22:00"),
        "min_meet": 30
    },
    "Lisa": {
        "location": "Union Square",
        "avail_start": time_to_minutes("9:00"),
        "avail_end": time_to_minutes("16:30"),
        "min_meet": 45
    },
    "Joshua": {
        "location": "Financial District",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("15:15"),
        "min_meet": 15
    },
    "Nancy": {
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("8:00"),
        "avail_end": time_to_minutes("11:30"),
        "min_meet": 90
    },
    "Andrew": {
        "location": "Nob Hill",
        "avail_start": time_to_minutes("11:30"),
        "avail_end": time_to_minutes("20:15"),
        "min_meet": 60
    },
    "John": {
        "location": "Bayview",
        "avail_start": time_to_minutes("16:45"),
        "avail_end": time_to_minutes("21:30"),
        "min_meet": 75
    }
}

# Starting point and time
start_location = "Embarcadero"
start_time = time_to_minutes("9:00")

# Function to look up travel times
def get_travel_time(origin, destination):
    return travel_times.get((origin, destination), float('inf'))

# We want to maximize number of meetings (i.e. friends met).
# We'll try all permutations and choose one that meets all constraints.
best_schedule = None
best_count = 0
best_finish = float('inf')
friends_list = list(friends.keys())

for perm in itertools.permutations(friends_list):
    cur_time = start_time
    cur_location = start_location
    itinerary = []
    feasible = True
    for friend in perm:
        info = friends[friend]
        travel_time = get_travel_time(cur_location, info["location"])
        arrival_time = cur_time + travel_time
        # The meeting can only start when friend is available.
        meeting_start = max(arrival_time, info["avail_start"])
        meeting_end = meeting_start + info["min_meet"]
        # Check if meeting can finish before friend leaves.
        if meeting_end > info["avail_end"]:
            feasible = False
            break
        # Append the meeting event to itinerary.
        event = {
            "action": "meet",
            "location": info["location"],
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        itinerary.append(event)
        cur_time = meeting_end
        cur_location = info["location"]
    if feasible:
        count = len(itinerary)
        # We want to maximize count and minimize final finish time.
        if count > best_count or (count == best_count and cur_time < best_finish):
            best_count = count
            best_finish = cur_time
            best_schedule = itinerary

# Prepare the result dictionary.
result = {"itinerary": best_schedule if best_schedule is not None else []}

# Output the result as JSON.
print(json.dumps(result, indent=2))
                    
if __name__ == '__main__':
    pass