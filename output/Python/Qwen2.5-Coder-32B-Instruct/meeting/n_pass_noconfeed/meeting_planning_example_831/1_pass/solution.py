import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Richmond District'): 21,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Richmond District'): 20,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Chinatown'): 29,
    ('Sunset District', 'Richmond District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Richmond District'): 21,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Richmond District'): 20,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Chinatown'): 20,
}

# Define the meetings
meetings = {
    'Jeffrey': {'location': 'Fisherman\'s Wharf', 'start': '10:15', 'end': '13:00', 'min_duration': 90},
    'Ronald': {'location': 'Alamo Square', 'start': '7:45', 'end': '14:45', 'min_duration': 120},
    'Jason': {'location': 'Financial District', 'start': '10:45', 'end': '16:00', 'min_duration': 105},
    'Melissa': {'location': 'Union Square', 'start': '17:45', 'end': '18:15', 'min_duration': 15},
    'Elizabeth': {'location': 'Sunset District', 'start': '14:45', 'end': '17:30', 'min_duration': 105},
    'Margaret': {'location': 'Embarcadero', 'start': '13:15', 'end': '19:00', 'min_duration': 90},
    'George': {'location': 'Golden Gate Park', 'start': '19:00', 'end': '22:00', 'min_duration': 75},
    'Richard': {'location': 'Chinatown', 'start': '9:30', 'end': '21:00', 'min_duration': 15},
    'Laura': {'location': 'Richmond District', 'start': '9:45', 'end': '18:00', 'min_duration': 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def find_meeting_schedule(meetings, travel_times):
    current_time = parse_time('9:00')
    current_location = 'Presidio'
    itinerary = []

    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for person, details in sorted_meetings:
        location = details['location']
        start_time = parse_time(details['start'])
        end_time = parse_time(details['end'])
        min_duration = details['min_duration']

        # Calculate travel time to the next meeting location
        travel_time = travel_times.get((current_location, location), float('inf'))

        # Calculate the earliest possible start time for the meeting
        earliest_start = max(current_time + timedelta(minutes=travel_time), start_time)

        # Calculate the latest possible end time for the meeting
        latest_end = end_time

        # Calculate the actual meeting duration
        actual_duration = min(latest_end - earliest_start, timedelta(minutes=min_duration))

        if actual_duration.total_seconds() >= min_duration * 60:
            # If we can meet for the required duration, add it to the itinerary
            itinerary.append({
                'action': 'meet',
                'location': location,
                'person': person,
                'start_time': format_time(earliest_start),
                'end_time': format_time(earliest_start + actual_duration)
            })
            # Update the current time and location
            current_time = earliest_start + actual_duration
            current_location = location

    return itinerary

itinerary = find_meeting_schedule(meetings, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))