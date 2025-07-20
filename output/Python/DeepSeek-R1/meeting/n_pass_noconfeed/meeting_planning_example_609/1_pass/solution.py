import json
from itertools import combinations, permutations
from collections import namedtuple

# Define travel times dictionary
travel_times = {
    "Chinatown": {
        "Mission District": 18,
        "Alamo Square": 17,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Golden Gate Park": 23,
        "Sunset District": 29,
        "Presidio": 19
    },
    "Mission District": {
        "Chinatown": 16,
        "Alamo Square": 11,
        "Pacific Heights": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Sunset District": 24,
        "Presidio": 25
    },
    "Alamo Square": {
        "Chinatown": 16,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Union Square": 14,
        "Golden Gate Park": 9,
        "Sunset District": 16,
        "Presidio": 18
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Mission District": 15,
        "Alamo Square": 10,
        "Union Square": 12,
        "Golden Gate Park": 15,
        "Sunset District": 21,
        "Presidio": 11
    },
    "Union Square": {
        "Chinatown": 7,
        "Mission District": 14,
        "Alamo Square": 15,
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "Sunset District": 26,
        "Presidio": 24
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Mission District": 17,
        "Alamo Square": 10,
        "Pacific Heights": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Presidio": 11
    },
    "Sunset District": {
        "Chinatown": 30,
        "Mission District": 24,
        "Alamo Square": 17,
        "Pacific Heights": 21,
        "Union Square": 30,
        "Golden Gate Park": 11,
        "Presidio": 16
    },
    "Presidio": {
        "Chinatown": 21,
        "Mission District": 26,
        "Alamo Square": 18,
        "Pacific Heights": 11,
        "Union Square": 22,
        "Golden Gate Park": 12,
        "Sunset District": 15
    }
}

# Add 0 travel time for same location
for loc in travel_times:
    travel_times[loc][loc] = 0

# Define friends (Carol is skipped because impossible to meet)
Friend = namedtuple('Friend', ['name', 'location', 'available_start', 'available_end', 'required_duration'])
friends = [
    Friend('David', 'Mission District', 480, 1185, 45),
    Friend('Kenneth', 'Alamo Square', 840, 1185, 120),
    Friend('John', 'Pacific Heights', 1020, 1200, 15),
    Friend('Charles', 'Union Square', 1305, 1365, 60),
    Friend('Deborah', 'Golden Gate Park', 420, 1095, 90),
    Friend('Karen', 'Sunset District', 1065, 1275, 15)
]

# Helper function to format minutes to time string
def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Initialize variables for best schedule
best_count = -1
best_itinerary = None
n = len(friends)

# Iterate from largest subset to smallest
found = False
for k in range(n, 0, -1):
    for subset in combinations(friends, k):
        for perm in permutations(subset):
            current_time = 540  # Start at 9:00 AM (540 minutes)
            current_location = "Chinatown"
            itinerary = []
            valid = True
            
            for friend in perm:
                # Get travel time
                travel = travel_times[current_location][friend.location]
                arrival = current_time + travel
                start_meeting = max(arrival, friend.available_start)
                end_meeting = start_meeting + friend.required_duration
                
                # Check if meeting fits in availability
                if end_meeting > friend.available_end:
                    valid = False
                    break
                
                # Record meeting
                itinerary.append({
                    'friend': friend,
                    'start': start_meeting,
                    'end': end_meeting
                })
                current_time = end_meeting
                current_location = friend.location
            
            # If valid schedule found with k meetings
            if valid:
                best_count = k
                best_itinerary = itinerary
                found = True
                break
        if found:
            break
    if found:
        break

# Build result JSON
if best_count == -1:
    result = {"itinerary": []}
else:
    itinerary_list = []
    for meeting in best_itinerary:
        f = meeting['friend']
        itinerary_list.append({
            "action": "meet",
            "location": f.location,
            "person": f.name,
            "start_time": format_time(meeting['start']),
            "end_time": format_time(meeting['end'])
        })
    result = {"itinerary": itinerary_list}

# Output as JSON
print(json.dumps(result))