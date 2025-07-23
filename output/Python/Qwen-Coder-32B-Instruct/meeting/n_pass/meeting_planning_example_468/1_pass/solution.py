import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
}

# Define the meeting constraints
meetings = {
    'Rebecca': {'location': 'Bayview', 'start': '9:00', 'end': '12:45', 'min_duration': 90},
    'Amanda': {'location': 'Pacific Heights', 'start': '18:30', 'end': '21:45', 'min_duration': 90},
    'James': {'location': 'Alamo Square', 'start': '9:45', 'end': '21:15', 'min_duration': 90},
    'Sarah': {'location': 'Fisherman\'s Wharf', 'start': '8:00', 'end': '21:30', 'min_duration': 90},
    'Melissa': {'location': 'Golden Gate Park', 'start': '9:00', 'end': '18:45', 'min_duration': 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes_to_time(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'The Castro'
    itinerary = []

    def visit(location, person, start, end, min_duration):
        nonlocal start_time, current_location, itinerary
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = add_minutes_to_time(start_time, travel_time)
        if arrival_time < start:
            arrival_time = start
        meeting_start = arrival_time
        meeting_end = add_minutes_to_time(meeting_start, min_duration)
        if meeting_end <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            start_time = meeting_end
            current_location = location

    # Prioritize meetings based on constraints
    visit('Bayview', 'Rebecca', parse_time('9:00'), parse_time('12:45'), 90)
    visit('Golden Gate Park', 'Melissa', parse_time('9:00'), parse_time('18:45'), 90)
    visit('Alamo Square', 'James', parse_time('9:45'), parse_time('21:15'), 90)
    visit('Fisherman\'s Wharf', 'Sarah', parse_time('8:00'), parse_time('21:30'), 90)
    visit('Pacific Heights', 'Amanda', parse_time('18:30'), parse_time('21:45'), 90)

    return itinerary

itinerary = find_optimal_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))