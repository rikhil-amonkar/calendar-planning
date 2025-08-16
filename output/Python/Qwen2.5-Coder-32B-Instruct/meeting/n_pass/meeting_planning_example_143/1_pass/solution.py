import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Embarcadero'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11
}

# Define the meeting constraints
constraints = {
    'Karen': {
        'location': 'Pacific Heights',
        'available_start': '18:45',
        'available_end': '20:15',
        'minimum_duration': 90
    },
    'Mark': {
        'location': 'Embarcadero',
        'available_start': '13:00',
        'available_end': '17:45',
        'minimum_duration': 120
    }
}

# Convert time strings to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate the end time of a meeting given a start time and duration
def calculate_end_time(start_time, duration):
    return start_time + timedelta(minutes=duration)

# Check if a meeting can fit within a person's availability
def can_meet(available_start, available_end, meeting_start, meeting_end):
    return available_start <= meeting_start and meeting_end <= available_end

# Main function to compute the optimal meeting schedule
def compute_schedule():
    current_location = 'North Beach'
    current_time = time_to_datetime('9:00')
    itinerary = []

    # Try to meet Mark first
    mark_constraint = constraints['Mark']
    mark_available_start = time_to_datetime(mark_constraint['available_start'])
    mark_available_end = time_to_datetime(mark_constraint['available_end'])
    mark_minimum_duration = mark_constraint['minimum_duration']
    mark_location = mark_constraint['location']

    # Calculate the earliest possible start time for Mark
    travel_to_mark = travel_times[(current_location, mark_location)]
    earliest_start_for_mark = current_time + timedelta(minutes=travel_to_mark)
    mark_meeting_start = max(earliest_start_for_mark, mark_available_start)
    mark_meeting_end = calculate_end_time(mark_meeting_start, mark_minimum_duration)

    # Check if we can meet Mark
    if can_meet(mark_available_start, mark_available_end, mark_meeting_start, mark_meeting_end):
        itinerary.append({
            "action": "meet",
            "location": mark_location,
            "person": "Mark",
            "start_time": mark_meeting_start.strftime('%H:%M'),
            "end_time": mark_meeting_end.strftime('%H:%M')
        })
        current_time = mark_meeting_end
        current_location = mark_location

    # Try to meet Karen next
    karen_constraint = constraints['Karen']
    karen_available_start = time_to_datetime(karen_constraint['available_start'])
    karen_available_end = time_to_datetime(karen_constraint['available_end'])
    karen_minimum_duration = karen_constraint['minimum_duration']
    karen_location = karen_constraint['location']

    # Calculate the earliest possible start time for Karen
    travel_to_karen = travel_times[(current_location, karen_location)]
    earliest_start_for_karen = current_time + timedelta(minutes=travel_to_karen)
    karen_meeting_start = max(earliest_start_for_karen, karen_available_start)
    karen_meeting_end = calculate_end_time(karen_meeting_start, karen_minimum_duration)

    # Check if we can meet Karen
    if can_meet(karen_available_start, karen_available_end, karen_meeting_start, karen_meeting_end):
        itinerary.append({
            "action": "meet",
            "location": karen_location,
            "person": "Karen",
            "start_time": karen_meeting_start.strftime('%H:%M'),
            "end_time": karen_meeting_end.strftime('%H:%M')
        })

    return json.dumps({"itinerary": itinerary})

# Output the result as JSON
print(compute_schedule())