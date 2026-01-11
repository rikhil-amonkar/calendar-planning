import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    'Financial District': {'Chinatown': 5, 'Alamo Square': 17, 'Bayview': 19, 'Fisherman\'s Wharf': 10},
    'Chinatown': {'Financial District': 5, 'Alamo Square': 17, 'Bayview': 22, 'Fisherman\'s Wharf': 8},
    'Alamo Square': {'Financial District': 17, 'Chinatown': 16, 'Bayview': 16, 'Fisherman\'s Wharf': 19},
    'Bayview': {'Financial District': 19, 'Chinatown': 18, 'Alamo Square': 16, 'Fisherman\'s Wharf': 25},
    'Fisherman\'s Wharf': {'Financial District': 11, 'Chinatown': 12, 'Alamo Square': 20, 'Bayview': 26}
}

# Constraints
constraints = {
    'Nancy': ('Chinatown', '9:30', '13:30', 90),
    'Mary': ('Alamo Square', '7:00', '21:00', 75),
    'Jessica': ('Bayview', '11:15', '13:45', 45),
    'Rebecca': ('Fisherman\'s Wharf', '7:00', '8:30', 45)
}

def parse_time(time_str):
    return int(time_str.split(':')[0]) * 60 + int(time_str.split(':')[1])

def format_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def is_valid_meeting(start, end, required_duration, person_constraints):
    avail_start, avail_end, required_duration_check = parse_time(person_constraints[1]), parse_time(person_constraints[2]), person_constraints[3]
    return avail_start <= start <= avail_end and avail_start <= end <= avail_end and (end - start) >= required_duration_check

def find_best_schedule(current_location, current_time, visited, itinerary):
    global best_itinerary
    if len(visited) == len(constraints):
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary[:]
        return
    
    for person, (location, start_time, end_time, required_duration) in constraints.items():
        if person not in visited:
            travel_time = travel_times[current_location][location]
            meeting_start = current_time + travel_time
            meeting_end = meeting_start + required_duration
            
            if is_valid_meeting(meeting_start, meeting_end, required_duration, constraints[person]):
                new_itinerary = itinerary + [{
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end)
                }]
                find_best_schedule(location, meeting_end, visited | {person}, new_itinerary)

best_itinerary = []
find_best_schedule('Financial District', parse_time('9:00'), set(), [])

result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))