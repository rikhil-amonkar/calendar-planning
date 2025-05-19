def time_to_min(timestr):
    h, m = map(int, timestr.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

arrival_golden = "9:00"
david_start_str = "16:00"
david_end_str = "21:45"
travel_time = 23
min_duration = 105

arrival_min = time_to_min(arrival_golden)
david_start = time_to_min(david_start_str)
david_end = time_to_min(david_end_str)

departure_golden = david_start - travel_time
itinerary = []

if departure_golden >= arrival_min:
    meeting_duration = david_end - david_start
    if meeting_duration >= min_duration:
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "David",
            "start_time": min_to_time(david_start),
            "end_time": min_to_time(david_end)
        })

import json
print(json.dumps({"itinerary": itinerary}))