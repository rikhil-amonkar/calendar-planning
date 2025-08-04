import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Mission District'): 24,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Mission District'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Mission District'): 16,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
}

# Define meeting constraints
meetings = {
    'Charles': {'location': 'Alamo Square', 'start': '18:00', 'end': '20:45', 'min_duration': 90},
    'Margaret': {'location': 'Russian Hill', 'start': '9:00', 'end': '16:00', 'min_duration': 30},
    'Daniel': {'location': 'Golden Gate Park', 'start': '8:00', 'end': '13:30', 'min_duration': 15},
    'Stephanie': {'location': 'Mission District', 'start': '20:30', 'end': '22:00', 'min_duration': 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, duration):
    return (parse_time(end) - parse_time(start)).total_seconds() / 60 >= duration

def find_schedule():
    current_location = 'Sunset District'
    current_time = parse_time('9:00')
    itinerary = []

    def visit(person, location, start, end, min_duration):
        nonlocal current_location, current_time
        travel_time = travel_times[(current_location, location)]
        arrival_time = add_minutes(current_time, travel_time)
        if arrival_time < parse_time(start):
            arrival_time = parse_time(start)
        leave_time = add_minutes(arrival_time, min_duration)
        if leave_time <= parse_time(end):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": arrival_time.strftime('%H:%M'),
                "end_time": leave_time.strftime('%H:%M')
            })
            current_location = location
            current_time = leave_time

    # Try to meet Margaret first since she leaves early
    visit('Margaret', meetings['Margaret']['location'], meetings['Margaret']['start'], meetings['Margaret']['end'], meetings['Margaret']['min_duration'])
    
    # Try to meet Daniel next
    visit('Daniel', meetings['Daniel']['location'], meetings['Daniel']['start'], meetings['Daniel']['end'], meetings['Daniel']['min_duration'])
    
    # Try to meet Charles in the evening
    visit('Charles', meetings['Charles']['location'], meetings['Charles']['start'], meetings['Charles']['end'], meetings['Charles']['min_duration'])
    
    # Try to meet Stephanie last
    visit('Stephanie', meetings['Stephanie']['location'], meetings['Stephanie']['start'], meetings['Stephanie']['end'], meetings['Stephanie']['min_duration'])

    return itinerary

itinerary = find_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))