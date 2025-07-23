import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Financial District'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10
}

# Define meeting constraints
meetings = {
    'Betty': {'location': 'Embarcadero', 'start': '19:45', 'end': '21:45', 'min_duration': 15},
    'Karen': {'location': 'Fisherman\'s Wharf', 'start': '8:45', 'end': '15:00', 'min_duration': 30},
    'Anthony': {'location': 'Financial District', 'start': '9:15', 'end': '21:30', 'min_duration': 105}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def find_meeting_schedule():
    start_time = parse_time('9:00')
    current_location = 'Bayview'
    itinerary = []

    def can_meet(meeting, current_time):
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        return current_time <= meeting_end - timedelta(minutes=meeting['min_duration'])

    def add_meeting_to_itinerary(person, location, start_time, duration):
        end_time = start_time + timedelta(minutes=duration)
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
        return end_time

    # Try to meet Karen first since she has the earliest availability
    if can_meet(meetings['Karen'], start_time):
        travel_time = travel_times[(current_location, meetings['Karen']['location'])]
        arrival_time = start_time + timedelta(minutes=travel_time)
        if arrival_time < parse_time(meetings['Karen']['end']):
            start_time = add_meeting_to_itinerary('Karen', meetings['Karen']['location'], arrival_time, meetings['Karen']['min_duration'])
            current_location = meetings['Karen']['location']

    # Try to meet Anthony next
    if can_meet(meetings['Anthony'], start_time):
        travel_time = travel_times[(current_location, meetings['Anthony']['location'])]
        arrival_time = start_time + timedelta(minutes=travel_time)
        if arrival_time < parse_time(meetings['Anthony']['end']):
            start_time = add_meeting_to_itinerary('Anthony', meetings['Anthony']['location'], arrival_time, meetings['Anthony']['min_duration'])
            current_location = meetings['Anthony']['location']

    # Finally, try to meet Betty
    if can_meet(meetings['Betty'], start_time):
        travel_time = travel_times[(current_location, meetings['Betty']['location'])]
        arrival_time = start_time + timedelta(minutes=travel_time)
        if arrival_time < parse_time(meetings['Betty']['end']):
            start_time = add_meeting_to_itinerary('Betty', meetings['Betty']['location'], arrival_time, meetings['Betty']['min_duration'])
            current_location = meetings['Betty']['location']

    return itinerary

itinerary = find_meeting_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result))