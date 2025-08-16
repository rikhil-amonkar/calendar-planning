import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Embarcadero'): 19,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
}

# Define meeting constraints
meetings = {
    'Thomas': {'location': 'Bayview', 'start': '15:30', 'end': '18:30', 'min_duration': 120},
    'Stephanie': {'location': 'Golden Gate Park', 'start': '18:30', 'end': '21:45', 'min_duration': 30},
    'Laura': {'location': 'Nob Hill', 'start': '8:45', 'end': '16:15', 'min_duration': 30},
    'Betty': {'location': 'Marina District', 'start': '18:45', 'end': '21:45', 'min_duration': 45},
    'Patricia': {'location': 'Embarcadero', 'start': '17:30', 'end': '22:00', 'min_duration': 45},
}

# Convert time strings to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if two time intervals overlap
def intervals_overlap(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

# Calculate the duration of overlap between two intervals
def overlap_duration(start1, end1, start2, end2):
    latest_start = max(start1, start2)
    earliest_end = min(end1, end2)
    return (earliest_end - latest_start).seconds // 60

# Find the optimal meeting schedule
def find_optimal_schedule():
    current_location = 'Fisherman\'s Wharf'
    current_time = time_to_datetime('9:00')
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: time_to_datetime(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start_time = time_to_datetime(details['start'])
        end_time = time_to_datetime(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]

        # Calculate potential meeting start time
        potential_start_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet the person for the required duration
        if intervals_overlap(potential_start_time, end_time, potential_start_time + timedelta(minutes=min_duration), end_time):
            # Calculate actual meeting start and end times
            meeting_start_time = potential_start_time
            meeting_end_time = meeting_start_time + timedelta(minutes=min_duration)

            # Add meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start_time.strftime('%H:%M'),
                "end_time": meeting_end_time.strftime('%H:%M')
            })

            # Update current location and time
            current_location = location
            current_time = meeting_end_time

    return itinerary

# Generate the optimal schedule
optimal_itinerary = find_optimal_schedule()

# Output the result as JSON
result = {
    "itinerary": optimal_itinerary
}
print(json.dumps(result))