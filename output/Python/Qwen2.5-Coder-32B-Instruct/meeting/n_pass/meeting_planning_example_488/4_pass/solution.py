import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15,
}

# Define the meeting constraints
constraints = {
    'Ronald': {'location': 'Nob Hill', 'start': '10:00', 'end': '17:00', 'min_duration': 105},
    'Sarah': {'location': 'Russian Hill', 'start': '7:15', 'end': '9:30', 'min_duration': 45},
    'Helen': {'location': 'The Castro', 'start': '13:30', 'end': '17:00', 'min_duration': 120},
    'Joshua': {'location': 'Sunset District', 'start': '14:15', 'end': '19:30', 'min_duration': 90},
    'Margaret': {'location': 'Haight-Ashbury', 'start': '10:15', 'end': '22:00', 'min_duration': 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M').time()

def time_to_str(dt):
    return dt.strftime('%H:%M')

def find_optimal_schedule(constraints, travel_times):
    current_time = datetime.strptime('09:00', '%H:%M').time()
    current_location = 'Pacific Heights'
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]['start']))

    for name, constraint in sorted_constraints:
        location = constraint['location']
        start = parse_time(constraint['start'])
        end = parse_time(constraint['end'])
        min_duration = constraint['min_duration']

        # Calculate travel time to the next location
        travel_time = travel_times.get((current_location, location), float('inf'))

        # Convert current_time to datetime for arithmetic operations
        current_datetime = datetime.combine(datetime.today(), current_time)
        travel_duration = timedelta(minutes=travel_time)
        arrival_time = current_datetime + travel_duration

        # Adjust arrival time if it's before the person's availability
        if arrival_time.time() < start:
            arrival_time = datetime.combine(datetime.today(), start)

        # Calculate the end time of the meeting
        meeting_end_time = arrival_time + timedelta(minutes=min_duration)

        # Ensure the meeting doesn't exceed the person's availability
        if meeting_end_time.time() > end:
            meeting_end_time = datetime.combine(datetime.today(), end) - timedelta(minutes=min_duration) + timedelta(minutes=min_duration)

        # If the meeting duration is less than the minimum required, skip this person
        if (meeting_end_time - arrival_time).total_seconds() / 60 < min_duration:
            continue

        # Add the meeting to the itinerary
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": time_to_str(arrival_time.time()),
            "end_time": time_to_str(meeting_end_time.time())
        })

        # Update current time and location
        current_time = meeting_end_time.time()
        current_location = location

    return itinerary

itinerary = find_optimal_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))