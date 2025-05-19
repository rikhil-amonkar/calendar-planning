import json
from itertools import permutations

def parse_time(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26, "Golden Gate Park": 25, "Embarcadero": 8,
        "Russian Hill": 7, "Nob Hill": 11, "Alamo Square": 20, "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24, "Golden Gate Park": 11, "Embarcadero": 22,
        "Russian Hill": 18, "Nob Hill": 16, "Alamo Square": 8, "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24, "The Castro": 13, "Embarcadero": 25,
        "Russian Hill": 19, "Nob Hill": 20, "Alamo Square": 10, "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6, "The Castro": 25, "Golden Gate Park": 25,
        "Russian Hill": 8, "Nob Hill": 10, "Alamo Square": 19, "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7, "The Castro": 21, "Golden Gate Park": 21,
        "Embarcadero": 8, "Nob Hill": 5, "Alamo Square": 15, "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11, "The Castro": 17, "Golden Gate Park": 17,
        "Embarcadero": 9, "Russian Hill": 5, "Alamo Square": 11, "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19, "The Castro": 8, "Golden Gate Park": 9,
        "Embarcadero": 17, "Russian Hill": 13, "Nob Hill": 11, "North Beach": 16
    },
    "North Beach": {
        "Fisherman's Wharf": 5, "The Castro": 22, "Golden Gate Park": 22,
        "Embarcadero": 6, "Russian Hill": 4, "Nob Hill": 7, "Alamo Square": 16
    }
}

friends = [
    {"name": "Joseph", "location": "Alamo Square", "start": parse_time("11:30"), "end": parse_time("12:45"), "duration": 15},
    {"name": "Karen", "location": "Russian Hill", "start": parse_time("14:30"), "end": parse_time("19:45"), "duration": 30},
    {"name": "Kimberly", "location": "North Beach", "start": parse_time("15:45"), "end": parse_time("19:15"), "duration": 30},
    {"name": "Laura", "location": "The Castro", "start": parse_time("19:45"), "end": parse_time("21:30"), "duration": 105},
    {"name": "Daniel", "location": "Golden Gate Park", "start": parse_time("21:15"), "end": parse_time("21:45"), "duration": 15}
]

best_schedule = []
max_met = 0

for perm in permutations(friends):
    current_loc = "Fisherman's Wharf"
    current_time = parse_time("9:00")
    schedule = []
    met = 0
    
    for friend in perm:
        to_loc = friend['location']
        travel_time = travel_times[current_loc].get(to_loc, float('inf'))
        if travel_time == float('inf'):
            break
        
        arrival = current_time + travel_time
        if arrival > friend['end']:
            continue
        
        start = max(arrival, friend['start'])
        end = start + friend['duration']
        if end > friend['end']:
            continue
        
        schedule.append((friend, start, end))
        met += 1
        current_time = end
        current_loc = to_loc
    
    if met > max_met or (met == max_met and current_time < (parse_time("23:59") if not best_schedule else best_schedule[-1][2])):
        max_met = met
        best_schedule = schedule

itinerary = []
for entry in best_schedule:
    friend, start, end = entry
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": format_time(start).replace(':0', ':') if format_time(start).split(':')[1][0] == '0' else format_time(start),
        "end_time": format_time(end).replace(':0', ':') if format_time(end).split(':')[1][0] == '0' else format_time(end)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))