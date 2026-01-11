import json
from datetime import datetime, timedelta

# Travel times between locations
travel_times = {
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Mission District'): 15,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Mission District'): 18,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 11,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Alamo Square'): 11,
}

# Meeting constraints
meetings = [
    {'name': 'Helen', 'location': 'North Beach', 'start': '9:00', 'end': '17:00', 'duration': 15},
    {'name': 'Kevin', 'location': 'Mission District', 'start': '10:45', 'end': '14:45', 'duration': 45},
    {'name': 'Amanda', 'location': 'Alamo Square', 'start': '19:45', 'end': '21:00', 'duration': 60},
    {'name': 'Betty', 'location': 'Financial District', 'start': '19:00', 'end': '21:45', 'duration': 90},
]

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def can_meet(current_time, current_location, meeting):
    meeting_start = time_to_minutes(meeting['start'])
    meeting_end = time_to_minutes(meeting['end'])
    travel_time = travel_times.get((current_location, meeting['location']), float('inf'))
    meeting_duration = meeting['duration']
    
    # Calculate the earliest possible start time for the meeting
    earliest_start = max(current_time + travel_time, meeting_start)
    
    # Check if there's enough time for the meeting
    if earliest_start + meeting_duration <= meeting_end:
        return True, earliest_start
    return False, None

def find_next_meeting(current_time, current_location, remaining_meetings):
    best_meeting = None
    best_start_time = None
    for meeting in remaining_meetings:
        can, start_time = can_meet(current_time, current_location, meeting)
        if can:
            if best_meeting is None or start_time < best_start_time:
                best_meeting = meeting
                best_start_time = start_time
    return best_meeting, best_start_time

def schedule_meetings():
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Pacific Heights'
    remaining_meetings = meetings.copy()
    
    while remaining_meetings:
        next_meeting, start_time = find_next_meeting(current_time, current_location, remaining_meetings)
        if next_meeting is None:
            break
        
        # Schedule the meeting
        end_time = start_time + next_meeting['duration']
        itinerary.append({
            "action": "meet",
            "location": next_meeting['location'],
            "person": next_meeting['name'],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        # Update current time and location
        current_time = end_time
        current_location = next_meeting['location']
        
        # Remove the scheduled meeting from the remaining list
        remaining_meetings.remove(next_meeting)
    
    return itinerary

# Generate the itinerary
itinerary = schedule_meetings()

# Output the result as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))