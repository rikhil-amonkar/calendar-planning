import itertools
import json

def time_to_min(timestr):
    """Convert 'H:MM' or 'HH:MM' to minutes since midnight."""
    if ':' not in timestr:
        return int(timestr) * 60  # if just hour given
    hour, minute = map(int, timestr.split(':'))
    return hour * 60 + minute

def min_to_time(m):
    """Convert minutes since midnight to 'H:MM' or 'HH:MM'."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes
locations = ["Golden Gate Park", "Haight-Ashbury", "Sunset District", "Marina District", "Financial District", "Union Square"]
# Index mapping
loc_index = {loc: i for i, loc in enumerate(locations)}

# Travel matrix from given data (order as above)
travel_matrix = [
    [0, 7, 10, 16, 26, 22],
    [7, 0, 15, 17, 21, 17],
    [11, 15, 0, 21, 30, 30],
    [18, 16, 19, 0, 17, 16],
    [23, 19, 31, 15, 0, 9],
    [22, 18, 26, 18, 9, 0]
]

def travel_time(from_loc, to_loc):
    return travel_matrix[loc_index[from_loc]][loc_index[to_loc]]

# Friends data: name, location, window_start, window_end, min_duration
friends = [
    ("Sarah", "Haight-Ashbury", time_to_min("17:00"), time_to_min("21:30"), 105),
    ("Patricia", "Sunset District", time_to_min("17:00"), time_to_min("19:45"), 45),
    ("Matthew", "Marina District", time_to_min("9:15"), time_to_min("12:00"), 15),
    ("Joseph", "Financial District", time_to_min("14:15"), time_to_min("18:45"), 30),
    ("Robert", "Union Square", time_to_min("10:15"), time_to_min("21:45"), 15)
]

# Start at Golden Gate Park at 9:00
start_time = time_to_min("9:00")
start_loc = "Golden Gate Park"

best_count = 0
best_schedule = []
best_itinerary = []

# Try all permutations of friends
for perm in itertools.permutations(friends):
    current_time = start_time
    current_loc = start_loc
    schedule = []
    met_count = 0
    possible = True
    
    for name, loc, win_start, win_end, min_dur in perm:
        # Travel to friend's location
        current_time += travel_time(current_loc, loc)
        # Arrival at friend's location
        arrival = current_time
        # Start meeting at max(arrival, win_start)
        meet_start = max(arrival, win_start)
        # Check if possible
        if meet_start + min_dur > win_end:
            possible = False
            break
        # Meet for min_duration
        meet_end = meet_start + min_dur
        schedule.append((name, loc, meet_start, meet_end))
        met_count += 1
        current_time = meet_end
        current_loc = loc
    
    if possible and met_count > best_count:
        best_count = met_count
        best_schedule = schedule
        best_itinerary = [{"action": "meet", "location": loc, "person": name, 
                           "start_time": min_to_time(s), "end_time": min_to_time(e)} 
                          for name, loc, s, e in schedule]

# Output result
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))