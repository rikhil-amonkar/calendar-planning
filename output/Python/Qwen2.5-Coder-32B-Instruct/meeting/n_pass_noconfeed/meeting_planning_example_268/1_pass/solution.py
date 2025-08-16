import json
from datetime import datetime, timedelta

# Define the travel times between locations
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

# Define the meeting constraints
meetings = {
    'Timothy': {'location': 'Alamo Square', 'start': '12:00', 'end': '16:15', 'min_duration': 105},
    'Mark': {'location': 'Presidio', 'start': '18:45', 'end': '21:00', 'min_duration': 60},
    'Joseph': {'location': 'Russian Hill', 'start': '16:45', 'end': '21:30', 'min_duration': 60},
}

# Convert time strings to datetime objects for easier manipulation
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate the end time of a meeting given its start time and duration
def calculate_end_time(start_time, duration):
    return start_time + timedelta(minutes=duration)

# Check if a meeting can fit within the available time slot
def can_meet(start_time, end_time, meeting_start, meeting_end):
    return start_time <= meeting_start and meeting_end <= end_time

# Find the best meeting time within the available time slot
def find_best_meeting_time(start_time, end_time, meeting_start, meeting_end, min_duration):
    meeting_start_dt = time_to_datetime(meeting_start)
    meeting_end_dt = time_to_datetime(meeting_end)
    available_start = max(start_time, meeting_start_dt)
    available_end = min(end_time, meeting_end_dt)
    if (available_end - available_start).total_seconds() / 60 >= min_duration:
        return available_start, calculate_end_time(available_start, min_duration)
    return None, None

# Main function to compute the optimal meeting schedule
def compute_schedule():
    current_location = 'Golden Gate Park'
    current_time = time_to_datetime('9:00')
    itinerary = []

    # Sort meetings by their latest possible start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: time_to_datetime(x[1]['end']))

    for person, details in sorted_meetings:
        location = details['location']
        meeting_start = details['start']
        meeting_end = details['end']
        min_duration = details['min_duration']

        # Calculate travel time to the next meeting location
        travel_time = travel_times[(current_location, location)]
        travel_end_time = calculate_end_time(current_time, travel_time)

        # Find the best meeting time within the available slot
        meeting_start_time, meeting_end_time = find_best_meeting_time(travel_end_time, time_to_datetime('21:30'), meeting_start, meeting_end, min_duration)

        if meeting_start_time and meeting_end_time:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start_time.strftime('%H:%M').lstrip('0'),
                "end_time": meeting_end_time.strftime('%H:%M').lstrip('0')
            })
            current_time = meeting_end_time
            current_location = location

    return itinerary

# Generate the JSON output
schedule = compute_schedule()
output = {
    "itinerary": schedule
}
print(json.dumps(output))