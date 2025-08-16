import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Financial District'): 17,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Embarcadero'): 4,
}

# Define meeting constraints
meetings = {
    'Joseph': {'location': 'Fisherman\'s Wharf', 'start': '8:00', 'end': '17:30', 'min_duration': 90},
    'Jeffrey': {'location': 'Bayview', 'start': '17:30', 'end': '21:30', 'min_duration': 60},
    'Kevin': {'location': 'Mission District', 'start': '11:15', 'end': '15:15', 'min_duration': 30},
    'David': {'location': 'Embarcadero', 'start': '8:15', 'end': '9:00', 'min_duration': 30},
    'Barbara': {'location': 'Financial District', 'start': '10:30', 'end': '16:30', 'min_duration': 15},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M')

def find_meeting_times(person, current_time):
    start = max(parse_time(meetings[person]['start']), current_time)
    end = min(parse_time(meetings[person]['end']), start + timedelta(minutes=meetings[person]['min_duration']))
    if end <= start:
        return None
    return start, end

def calculate_schedule():
    current_time = parse_time('9:00')
    itinerary = []
    current_location = 'Golden Gate Park'

    # List of people to meet, ordered by priority
    people_to_meet = ['David', 'Barbara', 'Kevin', 'Joseph', 'Jeffrey']

    for person in people_to_meet:
        meeting_info = meetings[person]
        location = meeting_info['location']
        travel_time = travel_times.get((current_location, location), float('inf'))

        # Check if we can reach the meeting location on time
        arrival_time = current_time + timedelta(minutes=travel_time)
        meeting_time = find_meeting_times(person, arrival_time)

        if meeting_time:
            itinerary.append({
                "action": "travel",
                "start_location": current_location,
                "end_location": location,
                "start_time": format_time(current_time),
                "end_time": format_time(arrival_time)
            })
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(meeting_time[0]),
                "end_time": format_time(meeting_time[1])
            })
            current_time = meeting_time[1]
            current_location = location

    return itinerary

schedule = calculate_schedule()
print(json.dumps({"itinerary": schedule}, indent=2))