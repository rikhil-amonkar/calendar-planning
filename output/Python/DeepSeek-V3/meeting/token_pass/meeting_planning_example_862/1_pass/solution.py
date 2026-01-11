import json
from itertools import permutations

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Travel times in minutes (symmetric but given fully, we'll store as dict)
travel_data = [
    ("Mission District", "Alamo Square", 11),
    ("Mission District", "Presidio", 25),
    ("Mission District", "Russian Hill", 15),
    ("Mission District", "North Beach", 17),
    ("Mission District", "Golden Gate Park", 17),
    ("Mission District", "Richmond District", 20),
    ("Mission District", "Embarcadero", 19),
    ("Mission District", "Financial District", 15),
    ("Mission District", "Marina District", 19),
    ("Alamo Square", "Mission District", 10),
    ("Alamo Square", "Presidio", 17),
    ("Alamo Square", "Russian Hill", 13),
    ("Alamo Square", "North Beach", 15),
    ("Alamo Square", "Golden Gate Park", 9),
    ("Alamo Square", "Richmond District", 11),
    ("Alamo Square", "Embarcadero", 16),
    ("Alamo Square", "Financial District", 17),
    ("Alamo Square", "Marina District", 15),
    ("Presidio", "Mission District", 26),
    ("Presidio", "Alamo Square", 19),
    ("Presidio", "Russian Hill", 14),
    ("Presidio", "North Beach", 18),
    ("Presidio", "Golden Gate Park", 12),
    ("Presidio", "Richmond District", 7),
    ("Presidio", "Embarcadero", 20),
    ("Presidio", "Financial District", 23),
    ("Presidio", "Marina District", 11),
    ("Russian Hill", "Mission District", 16),
    ("Russian Hill", "Alamo Square", 15),
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "North Beach", 5),
    ("Russian Hill", "Golden Gate Park", 21),
    ("Russian Hill", "Richmond District", 14),
    ("Russian Hill", "Embarcadero", 8),
    ("Russian Hill", "Financial District", 11),
    ("Russian Hill", "Marina District", 7),
    ("North Beach", "Mission District", 18),
    ("North Beach", "Alamo Square", 16),
    ("North Beach", "Presidio", 17),
    ("North Beach", "Russian Hill", 4),
    ("North Beach", "Golden Gate Park", 22),
    ("North Beach", "Richmond District", 18),
    ("North Beach", "Embarcadero", 6),
    ("North Beach", "Financial District", 8),
    ("North Beach", "Marina District", 9),
    ("Golden Gate Park", "Mission District", 17),
    ("Golden Gate Park", "Alamo Square", 9),
    ("Golden Gate Park", "Presidio", 11),
    ("Golden Gate Park", "Russian Hill", 19),
    ("Golden Gate Park", "North Beach", 23),
    ("Golden Gate Park", "Richmond District", 7),
    ("Golden Gate Park", "Embarcadero", 25),
    ("Golden Gate Park", "Financial District", 26),
    ("Golden Gate Park", "Marina District", 16),
    ("Richmond District", "Mission District", 20),
    ("Richmond District", "Alamo Square", 13),
    ("Richmond District", "Presidio", 7),
    ("Richmond District", "Russian Hill", 13),
    ("Richmond District", "North Beach", 17),
    ("Richmond District", "Golden Gate Park", 9),
    ("Richmond District", "Embarcadero", 19),
    ("Richmond District", "Financial District", 22),
    ("Richmond District", "Marina District", 9),
    ("Embarcadero", "Mission District", 20),
    ("Embarcadero", "Alamo Square", 19),
    ("Embarcadero", "Presidio", 20),
    ("Embarcadero", "Russian Hill", 8),
    ("Embarcadero", "North Beach", 5),
    ("Embarcadero", "Golden Gate Park", 25),
    ("Embarcadero", "Richmond District", 21),
    ("Embarcadero", "Financial District", 5),
    ("Embarcadero", "Marina District", 12),
    ("Financial District", "Mission District", 17),
    ("Financial District", "Alamo Square", 17),
    ("Financial District", "Presidio", 22),
    ("Financial District", "Russian Hill", 11),
    ("Financial District", "North Beach", 7),
    ("Financial District", "Golden Gate Park", 23),
    ("Financial District", "Richmond District", 21),
    ("Financial District", "Embarcadero", 4),
    ("Financial District", "Marina District", 15),
    ("Marina District", "Mission District", 20),
    ("Marina District", "Alamo Square", 15),
    ("Marina District", "Presidio", 10),
    ("Marina District", "Russian Hill", 8),
    ("Marina District", "North Beach", 11),
    ("Marina District", "Golden Gate Park", 18),
    ("Marina District", "Richmond District", 11),
    ("Marina District", "Embarcadero", 14),
    ("Marina District", "Financial District", 17),
]

# Build travel time dictionary
travel = {}
for a, b, t in travel_data:
    travel[(a, b)] = t

# Friends data: name, location, window start, window end, min duration (all in minutes)
friends = [
    ("Laura", "Alamo Square", time_to_minutes("14:30"), time_to_minutes("16:15"), 75),
    ("Brian", "Presidio", time_to_minutes("10:15"), time_to_minutes("17:00"), 30),
    ("Karen", "Russian Hill", time_to_minutes("18:00"), time_to_minutes("20:15"), 90),
    ("Stephanie", "North Beach", time_to_minutes("10:15"), time_to_minutes("16:00"), 75),
    ("Helen", "Golden Gate Park", time_to_minutes("11:30"), time_to_minutes("21:45"), 120),
    ("Sandra", "Richmond District", time_to_minutes("8:00"), time_to_minutes("15:15"), 30),
    ("Mary", "Embarcadero", time_to_minutes("16:45"), time_to_minutes("18:45"), 120),
    ("Deborah", "Financial District", time_to_minutes("19:00"), time_to_minutes("20:45"), 105),
    ("Elizabeth", "Marina District", time_to_minutes("8:30"), time_to_minutes("13:15"), 105),
]

# Start state
start_location = "Mission District"
start_time = time_to_minutes("9:00")

best_count = 0
best_itinerary = []
best_end_time = float('inf')

# DFS search
def dfs(current_loc, current_time, met_set, itinerary):
    global best_count, best_itinerary, best_end_time
    
    # Try to meet each un-met friend
    for idx, (name, loc, win_start, win_end, min_dur) in enumerate(friends):
        if idx in met_set:
            continue
        
        # Travel to friend
        travel_time = travel.get((current_loc, loc))
        if travel_time is None:
            # Try reverse
            travel_time = travel.get((loc, current_loc))
        if travel_time is None:
            continue
        
        arrive_time = current_time + travel_time
        if arrive_time > win_end:
            continue
        
        start_meeting = max(arrive_time, win_start)
        if start_meeting + min_dur > win_end:
            continue
        
        # Meet this friend
        new_met_set = met_set | {idx}
        new_itinerary = itinerary + [
            ("meet", loc, name, start_meeting, start_meeting + min_dur)
        ]
        
        # Recurse
        dfs(loc, start_meeting + min_dur, new_met_set, new_itinerary)
    
    # No more meetings possible
    if len(met_set) > best_count or (len(met_set) == best_count and current_time < best_end_time):
        best_count = len(met_set)
        best_itinerary = itinerary
        best_end_time = current_time

# Start DFS
dfs(start_location, start_time, set(), [])

# Convert to required JSON format
result = {"itinerary": []}
for action, location, person, start_m, end_m in best_itinerary:
    result["itinerary"].append({
        "action": action,
        "location": location,
        "person": person,
        "start_time": minutes_to_time(start_m),
        "end_time": minutes_to_time(end_m)
    })

print(json.dumps(result, indent=2))