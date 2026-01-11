import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t_str):
    """Convert 'H:MMAM/PM' to minutes past 9:00 AM."""
    # Input format like '9:00AM' or '3:30PM'
    t = datetime.strptime(t_str, '%I:%M%p')
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    """Convert minutes past midnight to 'H:MM' 24-hour format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times dictionary
travel = {
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Haight-Ashbury"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
}

# Friends data: name, location, window start, window end, min duration
friends = [
    ("Kimberly", "Presidio", "3:30PM", "4:00PM", 15),
    ("Elizabeth", "Alamo Square", "7:15PM", "8:15PM", 15),
    ("Joshua", "Marina District", "10:30AM", "2:15PM", 45),
    ("Sandra", "Financial District", "7:30PM", "8:15PM", 45),
    ("Kenneth", "Nob Hill", "12:45PM", "9:45PM", 30),
    ("Betty", "Sunset District", "2:00PM", "7:00PM", 60),
    ("Deborah", "Chinatown", "5:15PM", "8:30PM", 15),
    ("Barbara", "Russian Hill", "5:30PM", "9:15PM", 120),
    ("Steven", "North Beach", "5:45PM", "8:45PM", 90),
    ("Daniel", "Haight-Ashbury", "6:30PM", "6:45PM", 15),
]

# Convert times to minutes past 9:00 AM
base_time = time_to_minutes("9:00AM")
friends_converted = []
for name, loc, start, end, dur in friends:
    start_m = time_to_minutes(start) - base_time
    end_m = time_to_minutes(end) - base_time
    friends_converted.append((name, loc, start_m, end_m, dur))

# Search for best schedule
best_count = 0
best_schedule = []
best_total_duration = 0

# Try all permutations of friends (prune if too many, but 10 is manageable)
for perm in itertools.permutations(range(len(friends_converted))):
    current_loc = "Union Square"
    current_time = 0
    schedule = []
    count = 0
    total_duration = 0
    
    for idx in perm:
        name, loc, start_m, end_m, dur = friends_converted[idx]
        travel_time = travel.get((current_loc, loc))
        if travel_time is None:
            travel_time = travel.get((loc, current_loc))  # symmetric fallback
        # Earliest arrival at friend's location
        arrive = current_time + travel_time
        # Latest start time for meeting
        latest_start = end_m - dur
        if arrive > latest_start:
            continue  # cannot meet this friend
        # Start time is max(arrive, start_m)
        start_meeting = max(arrive, start_m)
        if start_meeting + dur > end_m:
            continue  # safety check
        # Schedule meeting
        schedule.append((name, loc, start_meeting, start_meeting + dur))
        count += 1
        total_duration += dur
        current_loc = loc
        current_time = start_meeting + dur
    
    # Evaluate this permutation
    if count > best_count or (count == best_count and total_duration > best_total_duration):
        best_count = count
        best_total_duration = total_duration
        best_schedule = schedule[:]

# Convert best schedule to output format
itinerary = []
for name, loc, start_m, end_m in best_schedule:
    start_str = minutes_to_time(start_m + base_time)
    end_str = minutes_to_time(end_m + base_time)
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": start_str,
        "end_time": end_str
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))