import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'The Castro'): 22,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'The Castro'): 7,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Mission District'): 7
}

# Define the constraints
constraints = {
    'James': {'location': 'Mission District', 'start_time': '12:45', 'end_time': '14:00', 'min_duration': 75},
    'Robert': {'location': 'The Castro', 'start_time': '12:45', 'end_time': '15:15', 'min_duration': 30}
}

# Convert time strings to datetime objects for easier manipulation
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Calculate the end time given a start time and duration in minutes
def calculate_end_time(start_time, duration):
    return start_time + timedelta(minutes=duration)

# Check if two time intervals overlap
def intervals_overlap(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

# Main function to compute the optimal meeting schedule
def compute_schedule():
    start_time = time_to_datetime('9:00')
    itinerary = []

    # Try to meet James first
    james_start = time_to_datetime(constraints['James']['start_time'])
    james_end = time_to_datetime(constraints['James']['end_time'])
    james_min_duration = constraints['James']['min_duration']

    # Calculate the earliest possible time to meet James
    earliest_james_meeting_start = max(start_time + timedelta(minutes=travel_times[('North Beach', 'Mission District')]), james_start)
    earliest_james_meeting_end = calculate_end_time(earliest_james_meeting_start, james_min_duration)

    # Check if we can meet James for the required duration
    if intervals_overlap(james_start, james_end, earliest_james_meeting_start, earliest_james_meeting_end):
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "James",
            "start_time": earliest_james_meeting_start.strftime('%H:%M'),
            "end_time": earliest_james_meeting_end.strftime('%H:%M')
        })
        current_location = 'Mission District'
        current_time = earliest_james_meeting_end
    else:
        # If we can't meet James, try to meet Robert instead
        current_location = 'North Beach'
        current_time = start_time

    # Try to meet Robert
    robert_start = time_to_datetime(constraints['Robert']['start_time'])
    robert_end = time_to_datetime(constraints['Robert']['end_time'])
    robert_min_duration = constraints['Robert']['min_duration']

    # Calculate the earliest possible time to meet Robert
    travel_to_robert = travel_times[(current_location, 'The Castro')]
    earliest_robert_meeting_start = max(current_time + timedelta(minutes=travel_to_robert), robert_start)
    earliest_robert_meeting_end = calculate_end_time(earliest_robert_meeting_start, robert_min_duration)

    # Check if we can meet Robert for the required duration
    if intervals_overlap(robert_start, robert_end, earliest_robert_meeting_start, earliest_robert_meeting_end):
        itinerary.append({
            "action": "meet",
            "location": "The Castro",
            "person": "Robert",
            "start_time": earliest_robert_meeting_start.strftime('%H:%M'),
            "end_time": earliest_robert_meeting_end.strftime('%H:%M')
        })

    return itinerary

# Generate the schedule and output it as JSON
schedule = compute_schedule()
output = {"itinerary": schedule}
print(json.dumps(output))