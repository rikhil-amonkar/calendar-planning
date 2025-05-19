import json
import itertools

travel_times = {
    "Pacific Heights": {"North Beach": 9, "Financial District": 13, "Alamo Square": 10, "Mission District": 15},
    "North Beach": {"Pacific Heights": 8, "Financial District": 8, "Alamo Square": 16, "Mission District": 18},
    "Financial District": {"Pacific Heights": 13, "North Beach": 7, "Alamo Square": 17, "Mission District": 17},
    "Alamo Square": {"Pacific Heights": 10, "North Beach": 15, "Financial District": 17, "Mission District": 10},
    "Mission District": {"Pacific Heights": 16, "North Beach": 17, "Financial District": 17, "Alamo Square": 11}
}

friends = [
    {"name": "Helen", "location": "North Beach", "start": 540, "end": 1020, "duration": 15},
    {"name": "Betty", "location": "Financial District", "start": 1140, "end": 1305, "duration": 90},
    {"name": "Amanda", "location": "Alamo Square", "start": 1185, "end": 1260, "duration": 60},
    {"name": "Kevin", "location": "Mission District", "start": 645, "end": 885, "duration": 45}
]

def minutes_to_time(m):
    return f"{m//60}:{m%60:02d}"

best = []
max_count = 0

for order in itertools.permutations(friends):
    current_loc = "Pacific Heights"
    current_time = 540
    itinerary = []
    
    for friend in order:
        travel = travel_times[current_loc].get(friend["location"], float('inf'))
        arrive = current_time + travel
        start = max(arrive, friend["start"])
        end = start + friend["duration"]
        
        if end > friend["end"]:
            continue
            
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        current_loc = friend["location"]
        current_time = end
    
    if len(itinerary) > max_count or (len(itinerary) == max_count and current_time < best_time):
        max_count = len(itinerary)
        best = itinerary
        best_time = current_time

print(json.dumps({"itinerary": best}, indent=2))