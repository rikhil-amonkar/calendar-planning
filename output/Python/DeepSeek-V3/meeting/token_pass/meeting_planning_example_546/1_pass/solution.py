import json
import itertools
from datetime import datetime, timedelta

def time_to_min(t):
    """Convert 'H:MM' string to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix
locations = ["Embarcadero", "Richmond District", "Union Square", 
             "Financial District", "Pacific Heights", "Nob Hill", "Bayview"]

travel = {
    "Embarcadero": {"Richmond District": 21, "Union Square": 10, "Financial District": 5,
                    "Pacific Heights": 11, "Nob Hill": 10, "Bayview": 21},
    "Richmond District": {"Embarcadero": 19, "Union Square": 21, "Financial District": 22,
                          "Pacific Heights": 10, "Nob Hill": 17, "Bayview": 26},
    "Union Square": {"Embarcadero": 11, "Richmond District": 20, "Financial District": 9,
                     "Pacific Heights": 15, "Nob Hill": 9, "Bayview": 15},
    "Financial District": {"Embarcadero": 4, "Richmond District": 21, "Union Square": 9,
                           "Pacific Heights": 13, "Nob Hill": 8, "Bayview": 19},
    "Pacific Heights": {"Embarcadero": 10, "Richmond District": 12, "Union Square": 12,
                        "Financial District": 13, "Nob Hill": 8, "Bayview": 22},
    "Nob Hill": {"Embarcadero": 9, "Richmond District": 14, "Union Square": 7,
                 "Financial District": 9, "Pacific Heights": 8, "Bayview": 19},
    "Bayview": {"Embarcadero": 19, "Richmond District": 25, "Union Square": 17,
                "Financial District": 19, "Pacific Heights": 23, "Nob Hill": 20}
}

# Friend data: name, location, window start, window end, min duration (all in minutes)
friends = [
    ("Kenneth", "Richmond District", time_to_min("21:15"), time_to_min("22:00"), 30),
    ("Lisa", "Union Square", time_to_min("9:00"), time_to_min("16:30"), 45),
    ("Joshua", "Financial District", time_to_min("12:00"), time_to_min("15:15"), 15),
    ("Nancy", "Pacific Heights", time_to_min("8:00"), time_to_min("11:30"), 90),
    ("Andrew", "Nob Hill", time_to_min("11:30"), time_to_min("20:15"), 60),
    ("John", "Bayview", time_to_min("16:45"), time_to_min("21:30"), 75)
]

# Start at Embarcadero at 9:00
start_time = time_to_min("9:00")
start_loc = "Embarcadero"

best_count = 0
best_total_time = 0
best_schedule = []

# Try all permutations of all subsets (size 1 to 6)
all_friends_indices = list(range(len(friends)))
for r in range(1, len(friends) + 1):
    for perm in itertools.permutations(all_friends_indices, r):
        current_time = start_time
        current_loc = start_loc
        met = []
        total_meeting_time = 0
        
        for idx in perm:
            name, loc, win_start, win_end, min_dur = friends[idx]
            travel_time = travel[current_loc][loc]
            arrive = current_time + travel_time
            if arrive > win_end:
                break  # can't meet this friend in this sequence
            start_meeting = max(arrive, win_start)
            if start_meeting + min_dur > win_end:
                break  # not enough time in window
            # Schedule meeting
            met.append((name, loc, start_meeting, start_meeting + min_dur))
            total_meeting_time += min_dur
            current_time = start_meeting + min_dur
            current_loc = loc
        
        # Evaluate this schedule
        if len(met) > best_count or (len(met) == best_count and total_meeting_time > best_total_time):
            best_count = len(met)
            best_total_time = total_meeting_time
            best_schedule = met

# Convert best_schedule to required JSON format
itinerary = []
for name, loc, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": min_to_time(start_m),
        "end_time": min_to_time(end_m)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))