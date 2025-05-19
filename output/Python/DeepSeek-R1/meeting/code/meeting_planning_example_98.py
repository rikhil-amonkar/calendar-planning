import json

def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Input parameters
arrival_al_time = '9:00'
tim_start_str = '20:45'
tim_end_str = '21:30'
travel_to_richmond = 12

arrival_al_min = time_to_min(arrival_al_time)
tim_start = time_to_min(tim_start_str)
tim_end = time_to_min(tim_end_str)
required_duration = 45

departure_al_min = tim_start - travel_to_richmond
itinerary = []

if (tim_end - tim_start) >= required_duration and departure_al_min >= arrival_al_min:
    itinerary.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Timothy",
        "start_time": min_to_time(tim_start),
        "end_time": min_to_time(tim_end)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))