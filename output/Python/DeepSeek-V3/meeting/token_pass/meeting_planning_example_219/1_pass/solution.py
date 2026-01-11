import json
from itertools import permutations

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def add_time(t, delta):
    """Add delta minutes to time string, return time string."""
    return minutes_to_time(time_to_minutes(t) + delta)

# Input data
start_location = "The Castro"
start_time = "9:00"

# Friends data: name, location, window_start, window_end, min_duration
friends = [
    ("Emily", "Alamo Square", "11:45", "15:15", 105),
    ("Barbara", "Union Square", "16:45", "18:15", 60),
    ("William", "Chinatown", "17:15", "19:00", 105)
]

# Travel times matrix (in minutes)
travel = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Chinatown"): 16,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Union Square"): 7,
}

def can_schedule(order):
    """Check if a given order of friends is feasible with min durations."""
    current_time = time_to_minutes(start_time)
    current_loc = start_location
    itinerary = []
    total_meeting_time = 0
    
    for name, loc, win_start, win_end, min_dur in order:
        # Travel to friend
        travel_time = travel.get((current_loc, loc))
        if travel_time is None:
            return None  # shouldn't happen
        current_time += travel_time
        
        # Check if we arrive before window ends
        win_start_m = time_to_minutes(win_start)
        win_end_m = time_to_minutes(win_end)
        
        if current_time > win_end_m:
            return None  # arrived too late
        
        # Start meeting as soon as possible after arrival and window start
        meet_start = max(current_time, win_start_m)
        if meet_start + min_dur > win_end_m:
            return None  # can't meet minimum
        
        # Meet for minimum duration
        meet_end = meet_start + min_dur
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        total_meeting_time += min_dur
        
        # Update current time and location
        current_time = meet_end
        current_loc = loc
    
    return itinerary, total_meeting_time

# Try all permutations of friends (1, 2, or 3 friends)
best_itinerary = None
best_total_time = -1

for r in range(1, len(friends) + 1):
    for perm in permutations(friends, r):
        result = can_schedule(perm)
        if result:
            itinerary, total_time = result
            if total_time > best_total_time:
                best_total_time = total_time
                best_itinerary = itinerary

# Output
output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))