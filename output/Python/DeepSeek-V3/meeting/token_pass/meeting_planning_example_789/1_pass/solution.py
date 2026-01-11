import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MMAM' or 'H:MMPM' to minutes since midnight."""
    if isinstance(t, str):
        t = t.strip().upper()
        if t.endswith("AM") or t.endswith("PM"):
            fmt = "%I:%M%p"
        else:
            fmt = "%H:%M"
        dt = datetime.strptime(t, fmt)
    else:
        dt = t
    return dt.hour * 60 + dt.minute

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes between locations
travel_times = {
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Sunset District"): 27,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Sunset District"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Sunset District"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
}

# Friends data: name, location, window start, window end, min_duration (minutes)
friends = [
    ("Betty", "Russian Hill", time_to_minutes("7:00AM"), time_to_minutes("4:45PM"), 105),
    ("Melissa", "Alamo Square", time_to_minutes("9:30AM"), time_to_minutes("5:15PM"), 105),
    ("Joshua", "Haight-Ashbury", time_to_minutes("12:15PM"), time_to_minutes("7:00PM"), 90),
    ("Jeffrey", "Marina District", time_to_minutes("12:15PM"), time_to_minutes("6:00PM"), 45),
    ("James", "Bayview", time_to_minutes("7:30AM"), time_to_minutes("8:00PM"), 90),
    ("Anthony", "Chinatown", time_to_minutes("11:45AM"), time_to_minutes("1:30PM"), 75),
    ("Timothy", "Presidio", time_to_minutes("12:30PM"), time_to_minutes("2:45PM"), 90),
    ("Emily", "Sunset District", time_to_minutes("7:30PM"), time_to_minutes("9:30PM"), 120),
]

# Start at Union Square at 9:00 AM
start_location = "Union Square"
start_time = time_to_minutes("9:00AM")

best_schedule = []
best_count = 0
best_total_meeting_time = 0

# Try all permutations of friends (max 8! = 40320, manageable with pruning)
all_friends_indices = list(range(len(friends)))

for perm in itertools.permutations(all_friends_indices):
    current_location = start_location
    current_time = start_time
    schedule = []
    met_count = 0
    total_meeting_time = 0
    
    feasible = True
    for idx in perm:
        name, loc, win_start, win_end, min_dur = friends[idx]
        # Travel time
        travel = travel_times.get((current_location, loc))
        if travel is None:
            travel = 0  # same location, but here all distinct so not needed
        
        arrival = current_time + travel
        # Start meeting at max(arrival, win_start)
        meet_start = max(arrival, win_start)
        if meet_start + min_dur > win_end:
            feasible = False
            break  # cannot meet this friend in this order
        
        meet_end = meet_start + min_dur
        schedule.append((name, loc, meet_start, meet_end))
        met_count += 1
        total_meeting_time += min_dur
        
        current_location = loc
        current_time = meet_end
    
    if feasible and (met_count > best_count or (met_count == best_count and total_meeting_time > best_total_meeting_time)):
        best_count = met_count
        best_total_meeting_time = total_meeting_time
        best_schedule = schedule

# Convert best schedule to required JSON format
itinerary = []
for name, loc, start_min, end_min in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(start_min),
        "end_time": minutes_to_time(end_min)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))