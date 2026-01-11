import json
from itertools import permutations
from datetime import datetime, timedelta

def parse_time(timestr):
    """Convert '9:00' or '19:45' to datetime today for easy arithmetic."""
    return datetime.strptime(timestr, "%H:%M")

def format_time(dt):
    """Convert datetime to 'H:MM' format."""
    return dt.strftime("%-H:%M")

def add_minutes(dt, minutes):
    return dt + timedelta(minutes=minutes)

# Travel times dictionary
travel_times = {
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Alamo Square"): 11,
}

# Friend data: name, location, window start, window end, min minutes
friends = [
    ("Helen", "North Beach", parse_time("9:00"), parse_time("17:00"), 15),
    ("Kevin", "Mission District", parse_time("10:45"), parse_time("14:45"), 45),
    ("Amanda", "Alamo Square", parse_time("19:45"), parse_time("21:00"), 60),
    ("Betty", "Financial District", parse_time("19:00"), parse_time("21:45"), 90),
]

start_location = "Pacific Heights"
start_time = parse_time("9:00")

best_schedule = None
best_friend_count = 0
best_total_meeting_minutes = 0

# Try all permutations of the 4 friends
for perm in permutations(range(4)):
    current_location = start_location
    current_time = start_time
    schedule = []
    met_friends = set()
    total_meeting_minutes = 0
    
    for idx in perm:
        name, loc, win_start, win_end, min_minutes = friends[idx]
        
        # Travel to friend's location
        travel_key = (current_location, loc)
        travel_min = travel_times.get(travel_key, 0)
        arrive_time = add_minutes(current_time, travel_min)
        
        # If we arrive before window start, wait
        if arrive_time < win_start:
            arrive_time = win_start
        
        # If we arrive too late to meet min minutes, skip this friend
        if arrive_time > add_minutes(win_end, -min_minutes):
            continue
        
        # Schedule meeting
        meeting_end = add_minutes(arrive_time, min_minutes)
        if meeting_end > win_end:
            continue  # Should not happen due to above check
        
        schedule.append((name, loc, arrive_time, meeting_end))
        met_friends.add(name)
        total_meeting_minutes += min_minutes
        
        # Update current location and time
        current_location = loc
        current_time = meeting_end
    
    # Evaluate this permutation
    friend_count = len(met_friends)
    if friend_count > best_friend_count or (friend_count == best_friend_count and total_meeting_minutes > best_total_meeting_minutes):
        best_friend_count = friend_count
        best_total_meeting_minutes = total_meeting_minutes
        best_schedule = schedule

# Convert best schedule to required JSON format
itinerary = []
for name, loc, start_dt, end_dt in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": format_time(start_dt),
        "end_time": format_time(end_dt)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))