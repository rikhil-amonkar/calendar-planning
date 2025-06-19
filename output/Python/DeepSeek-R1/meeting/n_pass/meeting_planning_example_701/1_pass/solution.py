# SOLUTION:

import itertools
import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    "Mission District": {"The Castro": 7, "Nob Hill": 12, "Presidio": 25, "Marina District": 19, "Pacific Heights": 16, "Golden Gate Park": 17, "Chinatown": 16, "Richmond District": 20},
    "The Castro": {"Mission District": 7, "Nob Hill": 16, "Presidio": 20, "Marina District": 21, "Pacific Heights": 16, "Golden Gate Park": 11, "Chinatown": 22, "Richmond District": 16},
    "Nob Hill": {"Mission District": 13, "The Castro": 17, "Presidio": 17, "Marina District": 11, "Pacific Heights": 8, "Golden Gate Park": 17, "Chinatown": 6, "Richmond District": 14},
    "Presidio": {"Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Marina District": 11, "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7},
    "Marina District": {"Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10, "Pacific Heights": 7, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11},
    "Pacific Heights": {"Mission District": 15, "The Castro": 16, "Nob Hill": 8, "Presidio": 11, "Marina District": 6, "Golden Gate Park": 15, "Chinatown": 11, "Richmond District": 12},
    "Golden Gate Park": {"Mission District": 17, "The Castro": 13, "Nob Hill": 20, "Presidio": 11, "Marina District": 16, "Pacific Heights": 16, "Chinatown": 23, "Richmond District": 7},
    "Chinatown": {"Mission District": 17, "The Castro": 22, "Nob Hill": 9, "Presidio": 19, "Marina District": 12, "Pacific Heights": 10, "Golden Gate Park": 23, "Richmond District": 20},
    "Richmond District": {"Mission District": 20, "The Castro": 16, "Nob Hill": 17, "Presidio": 7, "Marina District": 9, "Pacific Heights": 10, "Golden Gate Park": 9, "Chinatown": 20}
}

friends = [
    {"name": "Lisa", "location": "The Castro", "available_start": 1155, "available_end": 1275, "min_duration": 120},
    {"name": "Daniel", "location": "Nob Hill", "available_start": 495, "available_end": 660, "min_duration": 15},
    {"name": "Elizabeth", "location": "Presidio", "available_start": 1275, "available_end": 1335, "min_duration": 45},
    {"name": "Steven", "location": "Marina District", "available_start": 990, "available_end": 1245, "min_duration": 90},
    {"name": "Timothy", "location": "Pacific Heights", "available_start": 720, "available_end": 1080, "min_duration": 90},
    {"name": "Ashley", "location": "Golden Gate Park", "available_start": 1245, "available_end": 1305, "min_duration": 60},
    {"name": "Kevin", "location": "Chinatown", "available_start": 720, "available_end": 1140, "min_duration": 30},
    {"name": "Betty", "location": "Richmond District", "available_start": 795, "available_end": 945, "min_duration": 30}
]

start_time_minutes = 540
start_location = "Mission District"
best_count = 0
best_finish = None
best_itinerary = None

for r in range(8, 0, -1):
    current_r_best_finish = None
    current_r_best_itinerary = None
    for perm in itertools.permutations(friends, r):
        current_time = start_time_minutes
        current_location = start_location
        itinerary = []
        feasible = True
        
        for friend in perm:
            next_loc = friend["location"]
            travel = travel_times[current_location][next_loc]
            current_time += travel
            meeting_start = max(current_time, friend["available_start"])
            meeting_end = meeting_start + friend["min_duration"]
            
            if meeting_end > friend["available_end"]:
                feasible = False
                break
            
            itinerary.append({
                "friend": friend,
                "start": meeting_start,
                "end": meeting_end,
                "location": next_loc
            })
            current_time = meeting_end
            current_location = next_loc
        
        if feasible:
            if current_r_best_finish is None or current_time < current_r_best_finish:
                current_r_best_finish = current_time
                current_r_best_itinerary = itinerary
    
    if current_r_best_finish is not None:
        best_count = r
        best_finish = current_r_best_finish
        best_itinerary = current_r_best_itinerary
        break

result = {"itinerary": []}
if best_itinerary is not None:
    for meeting in best_itinerary:
        result["itinerary"].append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"]["name"],
            "start_time": format_time(meeting["start"]),
            "end_time": format_time(meeting["end"])
        })

print(json.dumps(result))