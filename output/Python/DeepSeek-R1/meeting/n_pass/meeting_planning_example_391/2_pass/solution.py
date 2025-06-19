import json
from itertools import permutations
from collections import namedtuple

# Define symmetric travel times between locations
travel_times = {
    "Sunset District": {
        "Alamo Square": 16,
        "Russian Hill": 24,
        "Presidio": 16,
        "Financial District": 30
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Presidio": 18,
        "Financial District": 17
    },
    "Russian Hill": {
        "Sunset District": 24,
        "Alamo Square": 13,
        "Presidio": 14,
        "Financial District": 11
    },
    "Presidio": {
        "Sunset District": 16,
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Financial District": 23
    },
    "Financial District": {
        "Sunset District": 30,
        "Alamo Square": 17,
        "Russian Hill": 11,
        "Presidio": 23
    }
}

# Define friends with corrected Thomas end time
Friend = namedtuple('Friend', ['name', 'location', 'start', 'end', 'duration'])
friends = [
    Friend("Kevin", "Alamo Square", 495, 1350, 75),
    Friend("Kimberly", "Russian Hill", 525, 750, 30),
    Friend("Joseph", "Presidio", 1110, 1155, 45),
    Friend("Thomas", "Financial District", 1260, 1425, 45)
]

start_time = 540  # 9:00 AM in minutes
start_location = "Sunset District"

# Generate all permutations of friends
best_count = 0
best_itinerary = None
best_total_travel = float('inf')

for perm in permutations(friends):
    current_time = start_time
    current_loc = start_location
    itinerary_perm = []
    
    for friend in perm:
        tt = travel_times[current_loc][friend.location]
        arrival_time = current_time + tt
        meeting_start = max(arrival_time, friend.start)
        meeting_end = meeting_start + friend.duration
        
        if meeting_end <= friend.end:
            itinerary_perm.append((friend, meeting_start, meeting_end))
            current_time = meeting_end
            current_loc = friend.location
        else:
            break  # This permutation won't work if any meeting can't be scheduled
    
    count = len(itinerary_perm)
    if count < len(perm):
        continue  # Skip incomplete permutations
    
    total_travel = 0
    prev_loc = start_location
    for meeting in itinerary_perm:
        friend = meeting[0]
        total_travel += travel_times[prev_loc][friend.location]
        prev_loc = friend.location
    # Add return trip to Sunset District
    total_travel += travel_times[prev_loc][start_location]
    
    if count > best_count or (count == best_count and total_travel < best_total_travel):
        best_count = count
        best_itinerary = itinerary_perm
        best_total_travel = total_travel

# Format the best itinerary as JSON
def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

itinerary_json = []
if best_itinerary is not None:
    for meeting in best_itinerary:
        friend, start_min, end_min = meeting
        itinerary_json.append({
            "action": "meet",
            "location": friend.location,
            "person": friend.name,
            "start_time": format_time(start_min),
            "end_time": format_time(end_min)
        })

output = {"itinerary": itinerary_json}
print(json.dumps(output))