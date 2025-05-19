import json

def time_to_min(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

arrival_sunset = "9:00"
joshua_start = "20:45"
joshua_end = "21:45"
travel_to_golden = 11
min_duration = 15

arrival_sunset_min = time_to_min(arrival_sunset)
j_start = time_to_min(joshua_start)
j_end = time_to_min(joshua_end)

departure = j_start - travel_to_golden
meeting_start = j_start
meeting_end = j_end

if departure >= arrival_sunset_min and (meeting_end - meeting_start) >= min_duration:
    itinerary = [{
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Joshua",
        "start_time": min_to_time(meeting_start),
        "end_time": min_to_time(meeting_end)
    }]
else:
    itinerary = []

print(json.dumps({"itinerary": itinerary}))