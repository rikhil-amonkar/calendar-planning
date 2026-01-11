import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Sunset District'): 16,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Sunset District'): 19,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Sunset District'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Sunset District'): 29,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Presidio'): 16,
}

# Define meeting constraints
meetings = {
    'Betty': {'location': 'Russian Hill', 'start': '7:00', 'end': '16:45', 'duration': 105},
    'Melissa': {'location': 'Alamo Square', 'start': '9:30', 'end': '17:15', 'duration': 105},
    'Joshua': {'location': 'Haight-Ashbury', 'start': '12:15', 'end': '19:00', 'duration': 90},
    'Jeffrey': {'location': 'Marina District', 'start': '12:15', 'end': '18:00', 'duration': 45},
    'James': {'location': 'Bayview', 'start': '7:30', 'end': '20:00', 'duration': 90},
    'Anthony': {'location': 'Chinatown', 'start': '11:45', 'end': '13:30', 'duration': 75},
    'Timothy': {'location': 'Presidio', 'start': '12:30', 'end': '14:45', 'duration': 90},
    'Emily': {'location': 'Sunset District', 'start': '19:30', 'end': '21:30', 'duration': 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, duration):
    return (end - start).total_seconds() / 60 >= duration

def find_schedule():
    current_time = parse_time('9:00')
    location = 'Union Square'
    itinerary = []

    # Convert all meeting times to datetime objects
    for person, details in meetings.items():
        details['start'] = parse_time(details['start'])
        details['end'] = parse_time(details['end'])

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: x[1]['start'])

    for person, details in sorted_meetings:
        if current_time >= details['end']:
            continue  # Skip if already too late

        travel_time = travel_times.get((location, details['location']), float('inf'))
        arrival_time = add_minutes(current_time, travel_time)

        if arrival_time >= details['end']:
            continue  # Skip if cannot arrive in time

        meeting_start = max(arrival_time, details['start'])
        meeting_end = add_minutes(meeting_start, details['duration'])

        if meeting_end > details['end']:
            continue  # Skip if meeting would end after person leaves

        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': details['location'],
            'person': person,
            'start_time': meeting_start.strftime('%H:%M'),
            'end_time': meeting_end.strftime('%H:%M')
        })

        # Update current time and location
        current_time = meeting_end
        location = details['location']

    return itinerary

# Generate and print the schedule
schedule = find_schedule()
result = {'itinerary': schedule}
print(json.dumps(result, indent=2))