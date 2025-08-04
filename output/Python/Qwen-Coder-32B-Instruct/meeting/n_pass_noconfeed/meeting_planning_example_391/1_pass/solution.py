import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Financial District'): 30,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Financial District'): 17,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Presidio'): 22,
}

# Define the meeting constraints
constraints = {
    'Kevin': {'location': 'Alamo Square', 'start': '8:15', 'end': '21:30', 'min_duration': 75},
    'Kimberly': {'location': 'Russian Hill', 'start': '8:45', 'end': '12:30', 'min_duration': 30},
    'Joseph': {'location': 'Presidio', 'start': '18:30', 'end': '19:15', 'min_duration': 45},
    'Thomas': {'location': 'Financial District', 'start': '19:00', 'end': '21:45', 'min_duration': 45},
}

# Convert time strings to datetime objects
def time_to_dt(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if a meeting can fit within the available time
def can_meet(start, end, min_duration):
    return (time_to_dt(end) - time_to_dt(start)).total_seconds() / 60 >= min_duration

# Calculate the next possible meeting time after traveling
def next_meeting_time(current_time, location, person):
    travel_time = travel_times[(current_location, location)]
    next_time = time_to_dt(current_time) + timedelta(minutes=travel_time)
    meeting_start = max(next_time, time_to_dt(constraints[person]['start']))
    meeting_end = min(meeting_start + timedelta(minutes=constraints[person]['min_duration']), time_to_dt(constraints[person]['end']))
    if can_meet(meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M'), constraints[person]['min_duration']):
        return meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M')
    return None, None

# Main function to find the optimal meeting schedule
def find_optimal_schedule():
    current_location = 'Sunset District'
    current_time = '9:00'
    itinerary = []

    # Try to meet each person in order of their availability
    for person in ['Kevin', 'Kimberly', 'Joseph', 'Thomas']:
        location = constraints[person]['location']
        meeting_start, meeting_end = next_meeting_time(current_time, location, person)
        if meeting_start and meeting_end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start,
                "end_time": meeting_end
            })
            current_time = meeting_end
            current_location = location

    return itinerary

# Generate the optimal schedule and output it as JSON
optimal_schedule = find_optimal_schedule()
output = {
    "itinerary": optimal_schedule
}
print(json.dumps(output))