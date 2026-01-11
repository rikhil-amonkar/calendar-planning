import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t_str):
    """Convert 'H:MMAM' or 'H:MMPM' to minutes since midnight."""
    try:
        # Handle possible 'AM'/'PM'
        t_str = t_str.strip().upper()
        if 'AM' in t_str or 'PM' in t_str:
            fmt = '%I:%M%p'
        else:
            fmt = '%H:%M'
        dt = datetime.strptime(t_str, fmt)
        return dt.hour * 60 + dt.minute
    except Exception as e:
        print(f"Error parsing time {t_str}: {e}")
        return 0

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix
locations = [
    "Alamo Square", "Russian Hill", "Presidio", "Chinatown",
    "Sunset District", "The Castro", "Embarcadero", "Golden Gate Park"
]

travel = {loc: {loc2: 0 for loc2 in locations} for loc in locations}

# Fill travel times (minutes)
data = [
    ("Alamo Square", "Russian Hill", 13),
    ("Alamo Square", "Presidio", 18),
    ("Alamo Square", "Chinatown", 16),
    ("Alamo Square", "Sunset District", 16),
    ("Alamo Square", "The Castro", 8),
    ("Alamo Square", "Embarcadero", 17),
    ("Alamo Square", "Golden Gate Park", 9),
    ("Russian Hill", "Alamo Square", 15),
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "Chinatown", 9),
    ("Russian Hill", "Sunset District", 23),
    ("Russian Hill", "The Castro", 21),
    ("Russian Hill", "Embarcadero", 8),
    ("Russian Hill", "Golden Gate Park", 21),
    ("Presidio", "Alamo Square", 18),
    ("Presidio", "Russian Hill", 14),
    ("Presidio", "Chinatown", 21),
    ("Presidio", "Sunset District", 15),
    ("Presidio", "The Castro", 21),
    ("Presidio", "Embarcadero", 20),
    ("Presidio", "Golden Gate Park", 12),
    ("Chinatown", "Alamo Square", 17),
    ("Chinatown", "Russian Hill", 7),
    ("Chinatown", "Presidio", 19),
    ("Chinatown", "Sunset District", 29),
    ("Chinatown", "The Castro", 22),
    ("Chinatown", "Embarcadero", 5),
    ("Chinatown", "Golden Gate Park", 23),
    ("Sunset District", "Alamo Square", 17),
    ("Sunset District", "Russian Hill", 24),
    ("Sunset District", "Presidio", 16),
    ("Sunset District", "Chinatown", 30),
    ("Sunset District", "The Castro", 17),
    ("Sunset District", "Embarcadero", 31),
    ("Sunset District", "Golden Gate Park", 11),
    ("The Castro", "Alamo Square", 8),
    ("The Castro", "Russian Hill", 18),
    ("The Castro", "Presidio", 20),
    ("The Castro", "Chinatown", 20),
    ("The Castro", "Sunset District", 17),
    ("The Castro", "Embarcadero", 22),
    ("The Castro", "Golden Gate Park", 11),
    ("Embarcadero", "Alamo Square", 19),
    ("Embarcadero", "Russian Hill", 8),
    ("Embarcadero", "Presidio", 20),
    ("Embarcadero", "Chinatown", 7),
    ("Embarcadero", "Sunset District", 30),
    ("Embarcadero", "The Castro", 25),
    ("Embarcadero", "Golden Gate Park", 25),
    ("Golden Gate Park", "Alamo Square", 10),
    ("Golden Gate Park", "Russian Hill", 19),
    ("Golden Gate Park", "Presidio", 11),
    ("Golden Gate Park", "Chinatown", 23),
    ("Golden Gate Park", "Sunset District", 10),
    ("Golden Gate Park", "The Castro", 13),
    ("Golden Gate Park", "Embarcadero", 25),
]

for from_loc, to_loc, t in data:
    travel[from_loc][to_loc] = t

# Friends data: name, location, start_available, end_available, min_duration (minutes)
friends = [
    ("Emily", "Russian Hill", "12:15PM", "2:15PM", 105),
    ("Mark", "Presidio", "2:45PM", "7:30PM", 60),
    ("Deborah", "Chinatown", "7:30AM", "3:30PM", 45),
    ("Margaret", "Sunset District", "9:30PM", "10:30PM", 60),
    ("George", "The Castro", "7:30AM", "2:15PM", 60),
    ("Andrew", "Embarcadero", "8:15PM", "10:00PM", 75),
    ("Steven", "Golden Gate Park", "11:15AM", "9:15PM", 105),
]

# Convert to minutes
friends_min = []
for name, loc, start_str, end_str, dur in friends:
    friends_min.append({
        "name": name,
        "location": loc,
        "start": time_to_minutes(start_str),
        "end": time_to_minutes(end_str),
        "min_dur": dur
    })

# Start at Alamo Square at 9:00
start_time = time_to_minutes("9:00AM")
start_loc = "Alamo Square"

best_count = 0
best_schedule = None
best_itinerary = []

# Try all subsets (except empty) and all permutations
for k in range(1, len(friends_min) + 1):
    for subset in itertools.combinations(range(len(friends_min)), k):
        for perm in itertools.permutations(subset):
            current_time = start_time
            current_loc = start_loc
            feasible = True
            itinerary = []
            for idx in perm:
                f = friends_min[idx]
                # Travel to friend's location
                travel_time = travel[current_loc][f["location"]]
                arrive_time = current_time + travel_time
                # Start meeting at max(arrive_time, friend's start)
                meet_start = max(arrive_time, f["start"])
                # Check if we can meet for min_duration
                if meet_start + f["min_dur"] > f["end"]:
                    feasible = False
                    break
                meet_end = meet_start + f["min_dur"]
                itinerary.append({
                    "action": "meet",
                    "location": f["location"],
                    "person": f["name"],
                    "start_time": minutes_to_time(meet_start),
                    "end_time": minutes_to_time(meet_end)
                })
                current_time = meet_end
                current_loc = f["location"]
            if feasible:
                if k > best_count:
                    best_count = k
                    best_schedule = perm
                    best_itinerary = itinerary

# Output result
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))