import json

def time_to_min(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def min_to_time(m):
    h, mm = divmod(m, 60)
    return f"{h}:{mm:02d}".replace(":0", ":") if mm < 10 else f"{h}:{mm}"

travel_times = {
    'Nob Hill': {'Pacific Heights': 8, 'Mission District': 13},
    'Pacific Heights': {'Nob Hill': 8, 'Mission District': 15},
    'Mission District': {'Nob Hill': 12, 'Pacific Heights': 16}
}

start_loc = 'Nob Hill'
start_time = time_to_min('9:00')

kenneth_loc = 'Mission District'
kenneth_start = time_to_min('12:00')
kenneth_end = time_to_min('15:45')
kenneth_duration = 45

thomas_loc = 'Pacific Heights'
thomas_start = time_to_min('15:30')
thomas_end = time_to_min('19:15')
thomas_duration = 75

itinerary = []

# Calculate Kenneth meeting
travel_to_k = travel_times[start_loc][kenneth_loc]
depart_k = max(kenneth_start - travel_to_k, start_time)
arrive_k = depart_k + travel_to_k
meet_k_end = arrive_k + kenneth_duration

if meet_k_end <= kenneth_end:
    itinerary.append({
        "action": "meet",
        "location": kenneth_loc,
        "person": "Kenneth",
        "start_time": min_to_time(arrive_k),
        "end_time": min_to_time(meet_k_end)
    })
    
    # Calculate Thomas meeting
    travel_to_t = travel_times[kenneth_loc][thomas_loc]
    depart_t = meet_k_end
    arrive_t = depart_t + travel_to_t
    start_t = max(arrive_t, thomas_start)
    end_t = start_t + thomas_duration
    
    if end_t <= thomas_end:
        itinerary.append({
            "action": "meet",
            "location": thomas_loc,
            "person": "Thomas",
            "start_time": min_to_time(start_t),
            "end_time": min_to_time(end_t)
        })

print(json.dumps({"itinerary": itinerary}, indent=2))