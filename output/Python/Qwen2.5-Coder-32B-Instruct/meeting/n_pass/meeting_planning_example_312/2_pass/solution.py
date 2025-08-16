import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
}

# Define meeting constraints
constraints = {
    'Sarah': {'location': 'Sunset District', 'start': '10:45', 'end': '19:00', 'min_duration': 30},
    'Richard': {'location': 'Haight-Ashbury', 'start': '11:45', 'end': '15:45', 'min_duration': 90},
    'Elizabeth': {'location': 'Mission District', 'start': '11:00', 'end': '17:15', 'min_duration': 120},
    'Michelle': {'location': 'Golden Gate Park', 'start': '18:15', 'end': '20:45', 'min_duration': 90},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M').time()

# Calculate the latest possible start time for a meeting
def latest_start(constraint):
    end_time = parse_time(constraint['end'])
    min_duration = constraint['min_duration']
    return (datetime.combine(datetime.today(), end_time) - timedelta(minutes=min_duration)).time()

# Calculate the earliest possible end time for a meeting
def earliest_end(constraint):
    start_time = parse_time(constraint['start'])
    min_duration = constraint['min_duration']
    return (datetime.combine(datetime.today(), start_time) + timedelta(minutes=min_duration)).time()

# Check if two time intervals overlap
def intervals_overlap(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

# Find the optimal meeting schedule
def find_schedule():
    current_location = 'Richmond District'
    current_time = datetime.strptime('09:00', '%H:%M').time()
    itinerary = []

    # Sort constraints by earliest possible start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    for name, constraint in sorted_constraints:
        location = constraint['location']
        start_constraint = parse_time(constraint['start'])
        end_constraint = parse_time(constraint['end'])
        min_duration = constraint['min_duration']

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]

        # Combine current time with today's date to perform time arithmetic
        current_datetime = datetime.combine(datetime.today(), current_time)
        travel_duration = timedelta(minutes=travel_time)
        arrival_datetime = current_datetime + travel_duration

        # Adjust arrival time if it's before the person's availability
        if arrival_datetime.time() < start_constraint:
            arrival_datetime = datetime.combine(datetime.today(), start_constraint)

        # Calculate the latest possible start time for the meeting
        latest_meeting_start = latest_start(constraint)

        # Determine the meeting start and end times
        meeting_start = max(arrival_datetime.time(), start_constraint)
        meeting_end = min(
            (datetime.combine(datetime.today(), meeting_start) + timedelta(minutes=min_duration)).time(),
            end_constraint,
            latest_meeting_start
        )

        # Ensure the meeting fits within the constraints
        if meeting_start <= meeting_end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end
            current_location = location

    return itinerary

# Generate the schedule and output it as JSON
schedule = find_schedule()
output = {"itinerary": schedule}
print(json.dumps(output))