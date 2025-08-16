import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

# Define meeting constraints
meetings = {
    'Jessica': {'location': 'Embarcadero', 'start': '16:45', 'end': '19:00', 'min_duration': 30},
    'Sandra': {'location': 'Richmond District', 'start': '18:30', 'end': '21:45', 'min_duration': 120},
    'Jason': {'location': 'Fisherman\'s Wharf', 'start': '16:00', 'end': '16:45', 'min_duration': 30},
}

# Convert time strings to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate travel time between two locations
def get_travel_time(start_location, end_location):
    return travel_times.get((start_location, end_location), float('inf'))

# Check if a meeting can fit within the given time slot
def can_fit_meeting(meeting_start, meeting_end, min_duration):
    return (time_to_datetime(meeting_end) - time_to_datetime(meeting_start)).total_seconds() / 60 >= min_duration

# Find the optimal meeting schedule
def find_optimal_schedule():
    current_time = time_to_datetime('9:00')
    current_location = 'Bayview'
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: time_to_datetime(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        meeting_start = details['start']
        meeting_end = details['end']
        min_duration = details['min_duration']

        # Calculate travel time to the meeting location
        travel_time = get_travel_time(current_location, location)

        # Calculate potential meeting start time after travel
        potential_meeting_start = current_time + timedelta(minutes=travel_time)

        # Check if we can attend this meeting
        if can_fit_meeting(potential_meeting_start.strftime('%H:%M'), meeting_end, min_duration):
            # Adjust meeting start time if it starts before the meeting window
            actual_meeting_start = max(potential_meeting_start, time_to_datetime(meeting_start))
            actual_meeting_end = actual_meeting_start + timedelta(minutes=min_duration)

            # Add meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": actual_meeting_start.strftime('%H:%M').lstrip('0'),
                "end_time": actual_meeting_end.strftime('%H:%M').lstrip('0')
            })

            # Update current time and location
            current_time = actual_meeting_end
            current_location = location

    return itinerary

# Generate the optimal schedule and output as JSON
optimal_schedule = find_optimal_schedule()
output = {
    "itinerary": optimal_schedule
}
print(json.dumps(output))