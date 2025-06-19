import itertools
import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    "Pacific Heights": {"North Beach": 9, "Financial District": 13, "Alamo Square": 10, "Mission District": 15},
    "North Beach": {"Pacific Heights": 8, "Financial District": 8, "Alamo Square": 16, "Mission District": 18},
    "Financial District": {"Pacific Heights": 13, "North Beach": 7, "Alamo Square": 17, "Mission District": 17},
    "Alamo Square": {"Pacific Heights": 10, "North Beach": 15, "Financial District": 17, "Mission District": 10},
    "Mission District": {"Pacific Heights": 16, "North Beach": 17, "Financial District": 17, "Alamo Square": 11}
}

meetings = [
    {"name": "Helen", "location": "North Beach", "start_avail": 540, "end_avail": 1020, "duration": 15},
    {"name": "Betty", "location": "Financial District", "start_avail": 1140, "end_avail": 1305, "duration": 90},
    {"name": "Amanda", "location": "Alamo Square", "start_avail": 1185, "end_avail": 1260, "duration": 60},
    {"name": "Kevin", "location": "Mission District", "start_avail": 645, "end_avail": 885, "duration": 45}
]

best_count = 0
best_itinerary = None

for perm in itertools.permutations(range(len(meetings))):
    current_time = 540
    current_location = "Pacific Heights"
    itinerary_perm = []
    
    for idx in perm:
        meeting = meetings[idx]
        tt = travel_times[current_location][meeting["location"]]
        arrival = current_time + tt
        start_meet = max(arrival, meeting["start_avail"])
        end_meet = start_meet + meeting["duration"]
        
        if end_meet <= meeting["end_avail"]:
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["name"],
                "start_time": format_time(start_meet),
                "end_time": format_time(end_meet)
            }
            itinerary_perm.append(event)
            current_time = end_meet
            current_location = meeting["location"]
    
    count = len(itinerary_perm)
    if count > best_count:
        best_count = count
        best_itinerary = itinerary_perm

result = {"itinerary": best_itinerary}
print(json.dumps(result))