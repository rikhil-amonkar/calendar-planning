import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Locations and travel times
locations = [
    "Chinatown", "Embarcadero", "Pacific Heights", "Russian Hill", 
    "Haight-Ashbury", "Golden Gate Park", "Fisherman's Wharf", 
    "Sunset District", "The Castro"
]

travel_times = {
    "Chinatown": {"Embarcadero": 5, "Pacific Heights": 10, "Russian Hill": 7, "Haight-Ashbury": 19, 
                  "Golden Gate Park": 23, "Fisherman's Wharf": 8, "Sunset District": 29, "The Castro": 22},
    "Embarcadero": {"Chinatown": 7, "Pacific Heights": 11, "Russian Hill": 8, "Haight-Ashbury": 21, 
                    "Golden Gate Park": 25, "Fisherman's Wharf": 6, "Sunset District": 30, "The Castro": 25},
    "Pacific Heights": {"Chinatown": 11, "Embarcadero": 10, "Russian Hill": 7, "Haight-Ashbury": 11, 
                        "Golden Gate Park": 15, "Fisherman's Wharf": 13, "Sunset District": 21, "The Castro": 16},
    "Russian Hill": {"Chinatown": 9, "Embarcadero": 8, "Pacific Heights": 7, "Haight-Ashbury": 17, 
                     "Golden Gate Park": 21, "Fisherman's Wharf": 7, "Sunset District": 23, "The Castro": 21},
    "Haight-Ashbury": {"Chinatown": 19, "Embarcadero": 20, "Pacific Heights": 12, "Russian Hill": 17, 
                       "Golden Gate Park": 7, "Fisherman's Wharf": 23, "Sunset District": 15, "The Castro": 6},
    "Golden Gate Park": {"Chinatown": 23, "Embarcadero": 25, "Pacific Heights": 16, "Russian Hill": 19, 
                         "Haight-Ashbury": 7, "Fisherman's Wharf": 24, "Sunset District": 10, "The Castro": 13},
    "Fisherman's Wharf": {"Chinatown": 12, "Embarcadero": 8, "Pacific Heights": 12, "Russian Hill": 7, 
                          "Haight-Ashbury": 22, "Golden Gate Park": 25, "Sunset District": 27, "The Castro": 27},
    "Sunset District": {"Chinatown": 30, "Embarcadero": 30, "Pacific Heights": 21, "Russian Hill": 24, 
                        "Haight-Ashbury": 15, "Golden Gate Park": 11, "Fisherman's Wharf": 29, "The Castro": 17},
    "The Castro": {"Chinatown": 22, "Embarcadero": 22, "Pacific Heights": 16, "Russian Hill": 18, 
                   "Haight-Ashbury": 6, "Golden Gate Park": 11, "Fisherman's Wharf": 24, "Sunset District": 17}
}

# Friends data
friends = [
    {"name": "Richard", "location": "Embarcadero", "start": "15:15", "end": "18:45", "duration": 90},
    {"name": "Mark", "location": "Pacific Heights", "start": "15:00", "end": "17:00", "duration": 45},
    {"name": "Matthew", "location": "Russian Hill", "start": "17:30", "end": "21:00", "duration": 90},
    {"name": "Rebecca", "location": "Haight-Ashbury", "start": "14:45", "end": "18:00", "duration": 60},
    {"name": "Melissa", "location": "Golden Gate Park", "start": "13:45", "end": "17:30", "duration": 90},
    {"name": "Margaret", "location": "Fisherman's Wharf", "start": "14:45", "end": "20:15", "duration": 15},
    {"name": "Emily", "location": "Sunset District", "start": "15:45", "end": "17:00", "duration": 45},
    {"name": "George", "location": "The Castro", "start": "14:00", "end": "16:15", "duration": 75}
]

def calculate_schedule(order):
    current_time = time_to_minutes("9:00")
    current_location = "Chinatown"
    schedule = []
    met_friends = set()
    
    for friend_name in order:
        friend = next(f for f in friends if f["name"] == friend_name)
        location = friend["location"]
        travel_time = travel_times[current_location][location]
        
        arrival_time = current_time + travel_time
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        duration = friend["duration"]
        
        # Calculate possible meeting start time
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + duration
        
        if meeting_end > end_window:
            # Try to start earlier if possible
            meeting_start = end_window - duration
            if meeting_start < start_window:
                continue  # Can't meet this friend
        
        if meeting_start < arrival_time:
            continue  # Can't meet this friend
        
        # Add to schedule
        schedule.append({
            "action": "meet",
            "location": location,
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        met_friends.add(friend["name"])
        current_time = meeting_end
        current_location = location
    
    return schedule, len(met_friends)

# Try different orders to maximize number of friends met
best_schedule = []
max_friends = 0

# We'll try permutations of friends who have earlier availability first to optimize
early_friends = ["George", "Melissa", "Margaret", "Rebecca", "Mark", "Richard", "Emily", "Matthew"]

# Try a reasonable number of permutations (not all 40320)
for _ in range(1000):
    import random
    random.shuffle(early_friends)
    schedule, count = calculate_schedule(early_friends)
    if count > max_friends:
        max_friends = count
        best_schedule = schedule
    if max_friends == 8:
        break

# Output the best schedule found
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))