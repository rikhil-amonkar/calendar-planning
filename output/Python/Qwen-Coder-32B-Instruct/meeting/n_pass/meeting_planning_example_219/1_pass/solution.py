import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

# Define the meeting constraints
meetings = {
    'Emily': {'location': 'Alamo Square', 'start': '11:45', 'end': '15:15', 'min_duration': 105},
    'Barbara': {'location': 'Union Square', 'start': '16:45', 'end': '18:15', 'min_duration': 60},
    'William': {'location': 'Chinatown', 'start': '17:15', 'end': '19:00', 'min_duration': 105},
}

# Convert time strings to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if a meeting can be scheduled within the person's availability
def can_meet(start, end, person_info):
    person_start = time_to_datetime(person_info['start'])
    person_end = time_to_datetime(person_info['end'])
    min_duration = timedelta(minutes=person_info['min_duration'])
    return start >= person_start and end <= person_end and (end - start) >= min_duration

# Find the optimal schedule
def find_optimal_schedule():
    start_time = time_to_datetime('9:00')
    current_location = 'The Castro'
    itinerary = []

    # Try to meet Emily
    emily_info = meetings['Emily']
    emily_start = time_to_datetime(emily_info['start'])
    emily_end = time_to_datetime(emily_info['end'])
    emily_min_duration = timedelta(minutes=emily_info['min_duration'])

    # Calculate the earliest possible start time for meeting Emily
    travel_to_emily = travel_times[(current_location, emily_info['location'])]
    earliest_emily_start = start_time + timedelta(minutes=travel_to_emily)
    if earliest_emily_start < emily_start:
        earliest_emily_start = emily_start

    # Calculate the latest possible end time for meeting Emily
    latest_emily_end = earliest_emily_start + emily_min_duration
    if latest_emily_end > emily_end:
        latest_emily_end = emily_end

    if can_meet(earliest_emily_start, latest_emily_end, emily_info):
        itinerary.append({
            "action": "meet",
            "location": emily_info['location'],
            "person": "Emily",
            "start_time": earliest_emily_start.strftime('%H:%M'),
            "end_time": latest_emily_end.strftime('%H:%M')
        })
        current_location = emily_info['location']
        start_time = latest_emily_end

    # Try to meet Barbara
    barbara_info = meetings['Barbara']
    barbara_start = time_to_datetime(barbara_info['start'])
    barbara_end = time_to_datetime(barbara_info['end'])
    barbara_min_duration = timedelta(minutes=barbara_info['min_duration'])

    # Calculate the earliest possible start time for meeting Barbara
    travel_to_barbara = travel_times[(current_location, barbara_info['location'])]
    earliest_barbara_start = start_time + timedelta(minutes=travel_to_barbara)
    if earliest_barbara_start < barbara_start:
        earliest_barbara_start = barbara_start

    # Calculate the latest possible end time for meeting Barbara
    latest_barbara_end = earliest_barbara_start + barbara_min_duration
    if latest_barbara_end > barbara_end:
        latest_barbara_end = barbara_end

    if can_meet(earliest_barbara_start, latest_barbara_end, barbara_info):
        itinerary.append({
            "action": "meet",
            "location": barbara_info['location'],
            "person": "Barbara",
            "start_time": earliest_barbara_start.strftime('%H:%M'),
            "end_time": latest_barbara_end.strftime('%H:%M')
        })
        current_location = barbara_info['location']
        start_time = latest_barbara_end

    # Try to meet William
    william_info = meetings['William']
    william_start = time_to_datetime(william_info['start'])
    william_end = time_to_datetime(william_info['end'])
    william_min_duration = timedelta(minutes=william_info['min_duration'])

    # Calculate the earliest possible start time for meeting William
    travel_to_william = travel_times[(current_location, william_info['location'])]
    earliest_william_start = start_time + timedelta(minutes=travel_to_william)
    if earliest_william_start < william_start:
        earliest_william_start = william_start

    # Calculate the latest possible end time for meeting William
    latest_william_end = earliest_william_start + william_min_duration
    if latest_william_end > william_end:
        latest_william_end = william_end

    if can_meet(earliest_william_start, latest_william_end, william_info):
        itinerary.append({
            "action": "meet",
            "location": william_info['location'],
            "person": "William",
            "start_time": earliest_william_start.strftime('%H:%M'),
            "end_time": latest_william_end.strftime('%H:%M')
        })

    return itinerary

# Generate the solution
solution = {
    "itinerary": find_optimal_schedule()
}

# Output the solution as JSON
print(json.dumps(solution))