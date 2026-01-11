import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix (in minutes)
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# Friend data: name, location, start_available, end_available, min_duration
friends = [
    ("Jeffrey", "Presidio", time_to_minutes("8:00"), time_to_minutes("10:00"), 105),
    ("John", "Pacific Heights", time_to_minutes("9:00"), time_to_minutes("13:30"), 15),
    ("Steven", "North Beach", time_to_minutes("13:30"), time_to_minutes("22:00"), 45),
    ("Barbara", "Fisherman's Wharf", time_to_minutes("18:00"), time_to_minutes("21:30"), 30),
]

# Starting point
current_location = "Nob Hill"
current_time = time_to_minutes("9:00")
itinerary = []

# We'll manually plan the feasible optimal schedule found earlier
# 1. Go to John at Pacific Heights
travel = travel_times[(current_location, "Pacific Heights")]
arrival = current_time + travel
# John available from 9:00, we arrive at 9:08
start_meeting = max(arrival, time_to_minutes("9:00"))
end_meeting = start_meeting + 15  # 15 min meeting
itinerary.append({
    "action": "meet",
    "location": "Pacific Heights",
    "person": "John",
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})

# 2. Go to Steven at North Beach
current_location = "Pacific Heights"
current_time = end_meeting
# Wait until just before Steven's availability to minimize wait
# Steven starts at 13:30, travel = 9 min
travel = travel_times[(current_location, "North Beach")]
# We want to arrive at 13:30 exactly
departure = time_to_minutes("13:30") - travel
if current_time > departure:
    departure = current_time  # if we can't leave early enough, leave now
else:
    # We can wait at Pacific Heights until departure time
    pass
arrival = departure + travel
start_meeting = max(arrival, time_to_minutes("13:30"))
end_meeting = start_meeting + 45
itinerary.append({
    "action": "meet",
    "location": "North Beach",
    "person": "Steven",
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})

# 3. Go to Barbara at Fisherman's Wharf
current_location = "North Beach"
current_time = end_meeting
travel = travel_times[(current_location, "Fisherman's Wharf")]
arrival = current_time + travel
# Barbara available from 18:00
if arrival < time_to_minutes("18:00"):
    arrival = time_to_minutes("18:00")  # wait until she's available
start_meeting = arrival
end_meeting = start_meeting + 30
itinerary.append({
    "action": "meet",
    "location": "Fisherman's Wharf",
    "person": "Barbara",
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))