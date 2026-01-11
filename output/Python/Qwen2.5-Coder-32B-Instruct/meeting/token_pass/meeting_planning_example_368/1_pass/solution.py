import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    'Bayview': {'Russian Hill': 23, 'Alamo Square': 16, 'North Beach': 21, 'Financial District': 19},
    'Russian Hill': {'Bayview': 23, 'Alamo Square': 15, 'North Beach': 5, 'Financial District': 11},
    'Alamo Square': {'Bayview': 16, 'Russian Hill': 15, 'North Beach': 16, 'Financial District': 17},
    'North Beach': {'Bayview': 22, 'Russian Hill': 4, 'Alamo Square': 16, 'Financial District': 7},
    'Financial District': {'Bayview': 19, 'Russian Hill': 10, 'Alamo Square': 17, 'Financial District': 7}
}

# Define meeting constraints
meetings = {
    'Joseph': {'location': 'Russian Hill', 'start': '8:30', 'end': '19:15', 'min_duration': 60},
    'Nancy': {'location': 'Alamo Square', 'start': '11:00', 'end': '16:00', 'min_duration': 90},
    'Jason': {'location': 'North Beach', 'start': '16:45', 'end': '21:45', 'min_duration': 15},
    'Jeffrey': {'location': 'Financial District', 'start': '10:30', 'end': '15:45', 'min_duration': 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def is_valid_meeting(start_time, end_time, meeting_start, meeting_end, min_duration):
    # Check if the meeting can fit within the person's availability
    meeting_start_time = parse_time(meeting_start)
    meeting_end_time = parse_time(meeting_end)
    proposed_end_time = add_minutes(start_time, min_duration)
    
    if start_time >= meeting_start_time and proposed_end_time <= meeting_end_time:
        return True
    return False

def find_possible_meetings(current_location, current_time):
    possible_meetings = []
    for person, details in meetings.items():
        location = details['location']
        meeting_start = details['start']
        meeting_end = details['end']
        min_duration = details['min_duration']
        
        travel_time = travel_times[current_location][location]
        potential_start_time = add_minutes(current_time, travel_time)
        
        if is_valid_meeting(potential_start_time, add_minutes(potential_start_time, min_duration), meeting_start, meeting_end, min_duration):
            possible_meetings.append((person, location, potential_start_time, min_duration))
    
    return possible_meetings

def generate_schedule(current_location, current_time, visited, itinerary):
    possible_meetings = find_possible_meetings(current_location, current_time)
    if not possible_meetings:
        return itinerary
    
    best_itinerary = itinerary[:]
    for person, location, start_time, duration in possible_meetings:
        if person not in visited:
            new_visited = visited.copy()
            new_visited.add(person)
            new_itinerary = itinerary.copy()
            new_itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": start_time.strftime('%H:%M'),
                "end_time": add_minutes(start_time, duration).strftime('%H:%M')
            })
            
            end_time = add_minutes(start_time, duration)
            next_itinerary = generate_schedule(location, end_time, new_visited, new_itinerary)
            
            if len(next_itinerary) > len(best_itinerary):
                best_itinerary = next_itinerary
    
    return best_itinerary

# Start from Bayview at 9:00 AM
start_location = 'Bayview'
start_time = parse_time('9:00')
visited = set()
initial_itinerary = []

best_itinerary = generate_schedule(start_location, start_time, visited, initial_itinerary)

# Output the best itinerary as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))