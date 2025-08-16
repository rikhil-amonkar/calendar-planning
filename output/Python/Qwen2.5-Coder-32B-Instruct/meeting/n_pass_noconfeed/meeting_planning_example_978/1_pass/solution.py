import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'The Castro'): 20,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'The Castro'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'The Castro'): 16,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 13,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Nob Hill'): 16,
}

# Define meeting constraints
meetings = {
    'Stephanie': {'location': 'Fisherman\'s Wharf', 'start': '15:30', 'end': '22:00', 'min_duration': 30},
    'Lisa': {'location': 'Financial District', 'start': '10:45', 'end': '17:15', 'min_duration': 15},
    'Melissa': {'location': 'Russian Hill', 'start': '17:00', 'end': '21:45', 'min_duration': 120},
    'Betty': {'location': 'Marina District', 'start': '10:45', 'end': '14:15', 'min_duration': 60},
    'Sarah': {'location': 'Richmond District', 'start': '16:15', 'end': '19:30', 'min_duration': 105},
    'Daniel': {'location': 'Pacific Heights', 'start': '18:30', 'end': '21:45', 'min_duration': 60},
    'Joshua': {'location': 'Haight-Ashbury', 'start': '9:00', 'end': '15:30', 'min_duration': 15},
    'Joseph': {'location': 'Presidio', 'start': '7:00', 'end': '13:00', 'min_duration': 45},
    'Andrew': {'location': 'Nob Hill', 'start': '19:45', 'end': '22:00', 'min_duration': 105},
    'John': {'location': 'The Castro', 'start': '13:15', 'end': '19:45', 'min_duration': 45},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if a meeting can be scheduled
def can_meet(start, end, min_duration):
    duration = (end - start).total_seconds() / 60
    return duration >= min_duration

# Calculate travel time between two locations
def travel_time(location1, location2):
    return travel_times.get((location1, location2), float('inf'))

# Main function to find the optimal schedule
def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'Embarcadero'
    itinerary = []
    available_meetings = meetings.copy()

    while available_meetings:
        next_meeting = None
        best_end_time = None

        for person, details in available_meetings.items():
            location = details['location']
            start = parse_time(details['start'])
            end = parse_time(details['end'])
            min_duration = details['min_duration']

            # Calculate travel time to the meeting location
            travel_to_location = travel_time(current_location, location)

            # Calculate potential start and end times for the meeting
            potential_start = max(start, start_time + timedelta(minutes=travel_to_location))
            potential_end = potential_start + timedelta(minutes=min_duration)

            # Check if the meeting can fit within the person's availability
            if can_meet(potential_start, end, min_duration) and (best_end_time is None or potential_end < best_end_time):
                next_meeting = person
                best_end_time = potential_end

        if next_meeting:
            details = available_meetings[next_meeting]
            location = details['location']
            start = parse_time(details['start'])
            end = parse_time(details['end'])
            min_duration = details['min_duration']

            # Calculate travel time to the meeting location
            travel_to_location = travel_time(current_location, location)

            # Calculate actual start and end times for the meeting
            actual_start = max(start, start_time + timedelta(minutes=travel_to_location))
            actual_end = actual_start + timedelta(minutes=min_duration)

            # Add the meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": next_meeting,
                "start_time": actual_start.strftime('%H:%M'),
                "end_time": actual_end.strftime('%H:%M')
            })

            # Update current location and start time
            current_location = location
            start_time = actual_end

            # Remove the meeting from the available meetings
            del available_meetings[next_meeting]
        else:
            break

    return itinerary

# Generate the optimal schedule
optimal_itinerary = find_optimal_schedule()

# Output the result as JSON
result = {
    "itinerary": optimal_itinerary
}

print(json.dumps(result))