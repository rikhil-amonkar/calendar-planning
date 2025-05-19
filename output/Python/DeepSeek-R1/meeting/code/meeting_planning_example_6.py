import json

def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

start_time = "9:00"
start_loc = "Fisherman's Wharf"
kenneth_loc = "Nob Hill"
travel_time = 11
k_start = "14:15"
k_end = "19:45"
required_duration = 90

current_min = time_to_min(start_time)
k_start_min = time_to_min(k_start)
k_end_min = time_to_min(k_end)

earliest_arrival = k_start_min
latest_arrival = k_end_min - required_duration

departure_min = earliest_arrival - travel_time

if departure_min < current_min:
    departure_min = current_min
    arrival_min = departure_min + travel_time
    if arrival_min > latest_arrival:
        meet = None
    else:
        meet_start = arrival_min
        meet_end = arrival_min + required_duration
else:
    meet_start = earliest_arrival
    meet_end = meet_start + required_duration

itinerary = []
if meet_start <= latest_arrival:
    itinerary.append({
        "action": "meet",
        "location": kenneth_loc,
        "person": "Kenneth",
        "start_time": min_to_time(meet_start),
        "end_time": min_to_time(meet_end)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))