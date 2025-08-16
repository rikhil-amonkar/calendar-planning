import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
}

# Define meeting constraints
meetings = {
    'Timothy': {'location': 'Alamo Square', 'start': '12:00', 'end': '16:15', 'min_duration': 105},
    'Mark': {'location': 'Presidio', 'start': '18:45', 'end': '21:00', 'min_duration': 60},
    'Joseph': {'location': 'Russian Hill', 'start': '16:45', 'end': '21:30', 'min_duration': 60},
}

# Convert times to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate the latest start time for a meeting
def latest_start(meeting, duration):
    end_time = parse_time(meeting['end'])
    return end_time - timedelta(minutes=duration)

# Calculate the earliest end time for a meeting
def earliest_end(meeting, duration):
    start_time = parse_time(meeting['start'])
    return start_time + timedelta(minutes=duration)

# Find the optimal meeting times
def find_meeting_times(current_time, current_location, meetings_left, itinerary):
    if not meetings_left:
        return itinerary
    
    best_itinerary = None
    for person, meeting in meetings_left.items():
        # Calculate the latest start and earliest end for this meeting
        latest_start_time = latest_start(meeting, meeting['min_duration'])
        earliest_end_time = earliest_end(meeting, meeting['min_duration'])
        
        # Check if we can reach the meeting location in time
        travel_time = travel_times[(current_location, meeting['location'])]
        potential_start_time = current_time + timedelta(minutes=travel_time)
        
        if potential_start_time <= latest_start_time:
            # Determine the actual meeting start and end times
            meeting_start_time = max(potential_start_time, parse_time(meeting['start']))
            meeting_end_time = min(meeting_start_time + timedelta(minutes=meeting['min_duration']), parse_time(meeting['end']))
            
            # Add this meeting to the itinerary
            new_itinerary = itinerary + [{
                "action": "meet",
                "location": meeting['location'],
                "person": person,
                "start_time": meeting_start_time.strftime('%H:%M'),
                "end_time": meeting_end_time.strftime('%H:%M')
            }]
            
            # Recursively find the best itinerary for the remaining meetings
            remaining_meetings = {k: v for k, v in meetings_left.items() if k != person}
            candidate_itinerary = find_meeting_times(meeting_end_time, meeting['location'], remaining_meetings, new_itinerary)
            
            # Update the best itinerary if the candidate is better
            if candidate_itinerary:
                if not best_itinerary or len(candidate_itinerary) > len(best_itinerary):
                    best_itinerary = candidate_itinerary
    
    return best_itinerary

# Initial conditions
start_time = parse_time('9:00')
start_location = 'Golden Gate Park'

# Find the optimal itinerary
optimal_itinerary = find_meeting_times(start_time, start_location, meetings, [])

# Output the result as JSON
print(json.dumps({"itinerary": optimal_itinerary}, indent=2))