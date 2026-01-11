import itertools
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
locations = ["Financial District", "Russian Hill", "Sunset District", "North Beach", "The Castro", "Golden Gate Park"]
# Index mapping: 0: Financial District, 1: Russian Hill, 2: Sunset District, 3: North Beach, 4: The Castro, 5: Golden Gate Park

travel_matrix = [
    [0, 10, 31, 7, 23, 23],   # Financial District to others
    [11, 0, 23, 5, 21, 21],   # Russian Hill to others
    [30, 24, 0, 29, 17, 11],  # Sunset District to others
    [8, 4, 27, 0, 22, 22],    # North Beach to others
    [20, 18, 17, 20, 0, 11],  # The Castro to others
    [26, 19, 10, 24, 13, 0]   # Golden Gate Park to others
]

# Friends data: name, location index, start_available, end_available, min_duration
friends = [
    ("Ronald", 1, time_to_minutes("13:45"), time_to_minutes("17:15"), 105),
    ("Patricia", 2, time_to_minutes("9:15"), time_to_minutes("22:00"), 60),
    ("Laura", 3, time_to_minutes("12:30"), time_to_minutes("12:45"), 15),
    ("Emily", 4, time_to_minutes("16:15"), time_to_minutes("18:30"), 60),
    ("Mary", 5, time_to_minutes("15:00"), time_to_minutes("16:30"), 60)
]

start_location = 0  # Financial District
start_time = time_to_minutes("9:00")

def schedule_meetings(sequence):
    """Given a sequence of friends (indices), return itinerary if feasible, else None."""
    current_loc = start_location
    current_time = start_time
    itinerary = []
    
    for idx in sequence:
        name, loc, avail_start, avail_end, dur = friends[idx]
        # Travel to friend
        travel = travel_matrix[current_loc][loc]
        arrival = current_time + travel
        # If we arrive before available start, wait
        start_meeting = max(arrival, avail_start)
        # Check if we can meet for full duration before they leave
        if start_meeting + dur > avail_end:
            return None  # Not enough time in window
        end_meeting = start_meeting + dur
        itinerary.append((name, loc, start_meeting, end_meeting))
        current_time = end_meeting
        current_loc = loc
    return itinerary

# Try all permutations of friends to maximize count
best_count = 0
best_itinerary = None

for k in range(5, 0, -1):  # Try meeting 5, then 4, etc.
    found = False
    for perm in itertools.permutations(range(5), k):
        itin = schedule_meetings(perm)
        if itin is not None:
            # Valid schedule found
            best_count = k
            best_itinerary = itin
            found = True
            break
    if found:
        break

# Convert best itinerary to required JSON format
result = {"itinerary": []}
loc_names = locations
for name, loc_idx, start_m, end_m in best_itinerary:
    result["itinerary"].append({
        "action": "meet",
        "location": loc_names[loc_idx],
        "person": name,
        "start_time": minutes_to_time(start_m),
        "end_time": minutes_to_time(end_m)
    })

print(json.dumps(result, indent=2))