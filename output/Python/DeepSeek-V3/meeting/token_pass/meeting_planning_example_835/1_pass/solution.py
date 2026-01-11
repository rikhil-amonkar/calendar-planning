import json
from itertools import permutations

def time_to_min(t_str):
    """Convert 'H:MMAM/PM' to minutes since midnight."""
    if 'AM' in t_str or 'PM' in t_str:
        t_str = t_str.replace('AM', '').replace('PM', '')
        if 'AM' in t_str or 'PM' in t_str:  # in case of leftover
            t_str = t_str.split()[0]
        hour, minute = map(int, t_str.split(':'))
        if 'PM' in t_str and hour != 12:
            hour += 12
        if 'AM' in t_str and hour == 12:
            hour = 0
    else:
        hour, minute = map(int, t_str.split(':'))
    return hour * 60 + minute

def min_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix
locations = [
    "Pacific Heights", "Golden Gate Park", "The Castro", "Bayview",
    "Marina District", "Union Square", "Sunset District", "Alamo Square",
    "Financial District", "Mission District"
]
loc_index = {loc: i for i, loc in enumerate(locations)}

# Travel times given in problem (minutes)
travel_matrix = [
    [0, 15, 16, 22, 6, 12, 21, 10, 13, 15],  # Pacific Heights
    [16, 0, 13, 23, 16, 22, 10, 9, 26, 17],  # Golden Gate Park
    [16, 11, 0, 19, 21, 19, 17, 8, 21, 7],   # The Castro
    [23, 22, 19, 0, 27, 18, 23, 16, 19, 13], # Bayview
    [7, 18, 22, 27, 0, 16, 19, 15, 17, 20],  # Marina District
    [15, 22, 17, 15, 18, 0, 27, 15, 9, 14],  # Union Square
    [21, 11, 17, 22, 21, 30, 0, 17, 30, 25], # Sunset District
    [10, 9, 8, 16, 15, 14, 16, 0, 17, 10],   # Alamo Square
    [13, 23, 20, 19, 15, 9, 30, 17, 0, 17],  # Financial District
    [16, 17, 7, 14, 19, 15, 24, 11, 15, 0]   # Mission District
]

def travel_time(from_loc, to_loc):
    return travel_matrix[loc_index[from_loc]][loc_index[to_loc]]

# Friends data: (name, location, window_start, window_end, min_duration_minutes)
friends = [
    ("Helen", "Golden Gate Park", "9:30AM", "12:15PM", 45),
    ("Steven", "The Castro", "8:15PM", "10:00PM", 105),
    ("Deborah", "Bayview", "8:30AM", "12:00PM", 30),
    ("Matthew", "Marina District", "9:15AM", "2:15PM", 45),
    ("Joseph", "Union Square", "2:15PM", "6:45PM", 120),
    ("Ronald", "Sunset District", "4:00PM", "8:45PM", 60),
    ("Robert", "Alamo Square", "6:30PM", "9:15PM", 120),
    ("Rebecca", "Financial District", "2:45PM", "4:15PM", 30),
    ("Elizabeth", "Mission District", "6:30PM", "9:00PM", 120)
]

# Convert times to minutes
friends_min = []
for name, loc, start, end, dur in friends:
    friends_min.append((
        name, loc,
        time_to_min(start),
        time_to_min(end),
        dur
    ))

# Start at Pacific Heights at 9:00 AM
start_time = time_to_min("9:00AM")
start_loc = "Pacific Heights"

def schedule_meeting_order(order):
    """Check if a given meeting order is feasible, return itinerary or None."""
    current_loc = start_loc
    current_time = start_time
    itinerary = []
    for name, loc, win_start, win_end, dur in order:
        # Travel to friend
        travel = travel_time(current_loc, loc)
        arrive_time = current_time + travel
        # Start time is max(arrive_time, win_start)
        start_meeting = max(arrive_time, win_start)
        # Check if we can meet for min duration
        if start_meeting + dur > win_end:
            return None  # Not enough time in window
        end_meeting = start_meeting + dur
        itinerary.append((name, loc, start_meeting, end_meeting))
        # Update current location and time
        current_loc = loc
        current_time = end_meeting
    return itinerary

# Try to meet as many friends as possible
found_schedule = None
for size in range(len(friends_min), 0, -1):
    # Generate all permutations of subsets of size 'size'
    from itertools import combinations, permutations
    for subset in combinations(friends_min, size):
        for perm in permutations(subset):
            itinerary = schedule_meeting_order(perm)
            if itinerary:
                found_schedule = itinerary
                break
        if found_schedule:
            break
    if found_schedule:
        break

# Convert to required JSON format
if found_schedule:
    result = {"itinerary": []}
    for name, loc, start_m, end_m in found_schedule:
        result["itinerary"].append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": min_to_time(start_m),
            "end_time": min_to_time(end_m)
        })
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))