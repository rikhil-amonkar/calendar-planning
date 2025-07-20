import itertools
import json

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel_time dictionary
travel_time = {
    "Chinatown": {
        "Embarcadero": 5,
        "Pacific Heights": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 8,
        "Sunset District": 29,
        "The Castro": 22
    },
    "Embarcadero": {
        "Chinatown": 7,
        "Pacific Heights": 11,
        "Russian Hill": 8,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Sunset District": 30,
        "The Castro": 25
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Embarcadero": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Sunset District": 21,
        "The Castro": 16
    },
    "Russian Hill": {
        "Chinatown": 9,
        "Embarcadero": 8,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Golden Gate Park": 21,
        "Fisherman's Wharf": 7,
        "Sunset District": 23,
        "The Castro": 21
    },
    "Haight-Ashbury": {
        "Chinatown": 19,
        "Embarcadero": 20,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "Sunset District": 15,
        "The Castro": 6
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Embarcadero": 25,
        "Pacific Heights": 16,
        "Russian Hill": 19,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Sunset District": 10,
        "The Castro": 13
    },
    "Fisherman's Wharf": {
        "Chinatown": 12,
        "Embarcadero": 8,
        "Pacific Heights": 12,
        "Russian Hill": 7,
        "Haight-Ashbury": 22,
        "Golden Gate Park": 25,
        "Sunset District": 27,
        "The Castro": 27
    },
    "Sunset District": {
        "Chinatown": 30,
        "Embarcadero": 30,
        "Pacific Heights": 21,
        "Russian Hill": 24,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "The Castro": 17
    },
    "The Castro": {
        "Chinatown": 22,
        "Embarcadero": 22,
        "Pacific Heights": 16,
        "Russian Hill": 18,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 24,
        "Sunset District": 17
    }
}

# Define meetings with converted times to minutes
meetings = [
    {"name": "Richard", "location": "Embarcadero", "window_start": 15*60+15, "window_end": 18*60+45, "min_duration": 90},
    {"name": "Mark", "location": "Pacific Heights", "window_start": 15*60, "window_end": 17*60, "min_duration": 45},
    {"name": "Matthew", "location": "Russian Hill", "window_start": 17*60+30, "window_end": 21*60, "min_duration": 90},
    {"name": "Rebecca", "location": "Haight-Ashbury", "window_start": 14*60+45, "window_end": 18*60, "min_duration": 60},
    {"name": "Melissa", "location": "Golden Gate Park", "window_start": 13*60+45, "window_end": 17*60+30, "min_duration": 90},
    {"name": "Margaret", "location": "Fisherman's Wharf", "window_start": 14*60+45, "window_end": 20*60+15, "min_duration": 15},
    {"name": "Emily", "location": "Sunset District", "window_start": 15*60+45, "window_end": 17*60, "min_duration": 45},
    {"name": "George", "location": "The Castro", "window_start": 14*60, "window_end": 16*60+15, "min_duration": 75}
]

start_time_minutes = 9 * 60  # 9:00 AM
start_location = "Chinatown"
best_schedule = None

# Try from 8 meetings down to 1
for k in range(len(meetings), 0, -1):
    for perm in itertools.permutations(meetings, k):
        current_time = start_time_minutes
        current_loc = start_location
        schedule = []
        feasible = True
        
        for meeting in perm:
            loc = meeting["location"]
            travel = travel_time[current_loc][loc]
            arrival = current_time + travel
            start = max(arrival, meeting["window_start"])
            end = start + meeting["min_duration"]
            
            if end > meeting["window_end"]:
                feasible = False
                break
                
            schedule.append((meeting, start, end))
            current_time = end
            current_loc = loc
        
        if feasible:
            best_schedule = schedule
            break
    if best_schedule:
        break

# Convert to itinerary
itinerary = []
if best_schedule:
    for meeting, start, end in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))