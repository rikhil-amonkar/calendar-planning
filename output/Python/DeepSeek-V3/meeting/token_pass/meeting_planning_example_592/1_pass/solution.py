import itertools
import json
from collections import defaultdict

def time_to_min(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def min_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes: from -> to -> minutes
travel = defaultdict(dict)

dist_data = [
    ("North Beach", "Pacific Heights", 8),
    ("North Beach", "Chinatown", 6),
    ("North Beach", "Union Square", 7),
    ("North Beach", "Mission District", 18),
    ("North Beach", "Golden Gate Park", 22),
    ("North Beach", "Nob Hill", 7),
    ("Pacific Heights", "North Beach", 9),
    ("Pacific Heights", "Chinatown", 11),
    ("Pacific Heights", "Union Square", 12),
    ("Pacific Heights", "Mission District", 15),
    ("Pacific Heights", "Golden Gate Park", 15),
    ("Pacific Heights", "Nob Hill", 8),
    ("Chinatown", "North Beach", 3),
    ("Chinatown", "Pacific Heights", 10),
    ("Chinatown", "Union Square", 7),
    ("Chinatown", "Mission District", 18),
    ("Chinatown", "Golden Gate Park", 23),
    ("Chinatown", "Nob Hill", 8),
    ("Union Square", "North Beach", 10),
    ("Union Square", "Pacific Heights", 15),
    ("Union Square", "Chinatown", 7),
    ("Union Square", "Mission District", 14),
    ("Union Square", "Golden Gate Park", 22),
    ("Union Square", "Nob Hill", 9),
    ("Mission District", "North Beach", 17),
    ("Mission District", "Pacific Heights", 16),
    ("Mission District", "Chinatown", 16),
    ("Mission District", "Union Square", 15),
    ("Mission District", "Golden Gate Park", 17),
    ("Mission District", "Nob Hill", 12),
    ("Golden Gate Park", "North Beach", 24),
    ("Golden Gate Park", "Pacific Heights", 16),
    ("Golden Gate Park", "Chinatown", 23),
    ("Golden Gate Park", "Union Square", 22),
    ("Golden Gate Park", "Mission District", 17),
    ("Golden Gate Park", "Nob Hill", 20),
    ("Nob Hill", "North Beach", 8),
    ("Nob Hill", "Pacific Heights", 8),
    ("Nob Hill", "Chinatown", 6),
    ("Nob Hill", "Union Square", 7),
    ("Nob Hill", "Mission District", 13),
    ("Nob Hill", "Golden Gate Park", 17),
]

for frm, to, d in dist_data:
    travel[frm][to] = d

# Friends data: name -> (location, window_start, window_end, min_duration)
friends = {
    "James": ("Pacific Heights", time_to_min("20:00"), time_to_min("22:00"), 120),
    "Robert": ("Chinatown", time_to_min("12:15"), time_to_min("16:45"), 90),
    "Jeffrey": ("Union Square", time_to_min("9:30"), time_to_min("15:30"), 120),
    "Carol": ("Mission District", time_to_min("18:15"), time_to_min("21:15"), 15),
    "Mark": ("Golden Gate Park", time_to_min("11:30"), time_to_min("17:45"), 15),
    "Sandra": ("Nob Hill", time_to_min("8:00"), time_to_min("15:30"), 15),
}

start_location = "North Beach"
start_time = time_to_min("9:00")

def schedule_meeting_order(order):
    """Try to schedule given order of friends, return (success, itinerary, total_met)."""
    current_loc = start_location
    current_time = start_time
    itinerary = []
    met_count = 0
    
    for name in order:
        loc, win_start, win_end, min_dur = friends[name]
        # Travel to this friend
        travel_time = travel[current_loc][loc]
        arrive = current_time + travel_time
        
        # If we arrive after window end, cannot meet
        if arrive > win_end:
            return False, [], 0
        
        # Start meeting at max(arrive, win_start)
        meet_start = max(arrive, win_start)
        meet_end = meet_start + min_dur
        
        # Check if meeting fits in window
        if meet_end > win_end:
            return False, [], 0
        
        # Special case: James must be exactly 20:00–22:00
        if name == "James":
            if meet_start != time_to_min("20:00"):
                return False, [], 0
            meet_end = time_to_min("22:00")
        
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": min_to_time(meet_start),
            "end_time": min_to_time(meet_end)
        })
        
        met_count += 1
        current_time = meet_end
        current_loc = loc
    
    return True, itinerary, met_count

# Try all permutations of all 6 friends
best_met = 0
best_itinerary = []

all_friends = list(friends.keys())

# We'll try permutations of all 6, but James must be at 20:00, so ordering around that is constrained.
# Better: brute-force permutations, but enforce James's fixed slot by checking during scheduling.
for perm in itertools.permutations(all_friends):
    success, itinerary, met = schedule_meeting_order(perm)
    if success and met > best_met:
        best_met = met
        best_itinerary = itinerary

# If best_met < 6, try subsets of size 5, 4, etc., but given constraints, likely max is 5.
# But let's first see if we found 6.
if best_met < 6:
    # Try subsets
    for size in range(5, 0, -1):
        for subset in itertools.combinations(all_friends, size):
            for perm in itertools.permutations(subset):
                success, itinerary, met = schedule_meeting_order(perm)
                if success and met > best_met:
                    best_met = met
                    best_itinerary = itinerary
        if best_met == size:  # Found max for this size
            break

# Output result
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))