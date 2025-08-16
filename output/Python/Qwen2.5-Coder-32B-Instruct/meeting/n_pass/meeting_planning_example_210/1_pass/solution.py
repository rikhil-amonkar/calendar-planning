import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Financial District'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21
}

# Define meeting constraints
meetings = {
    'Emily': {'location': 'Presidio', 'start': '16:15', 'end': '21:00', 'min_duration': 105},
    'Joseph': {'location': 'Richmond District', 'start': '17:15', 'end': '22:00', 'min_duration': 120},
    'Melissa': {'location': 'Financial District', 'start': '15:45', 'end': '21:45', 'min_duration': 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(dt):
    return dt.strftime('%H:%M')

def find_meeting_schedule():
    start_time = parse_time('9:00')
    current_location = 'Fisherman\'s Wharf'
    itinerary = []

    def can_meet(person, current_time):
        meeting = meetings[person]
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        return meeting_start <= current_time < meeting_end

    def get_meeting_end_time(person, start_time):
        meeting = meetings[person]
        min_duration = timedelta(minutes=meeting['min_duration'])
        return start_time + min_duration

    def travel_time(from_loc, to_loc):
        return timedelta(minutes=travel_times[(from_loc, to_loc)])

    def try_meeting(person, current_time, current_location):
        if can_meet(person, current_time):
            meeting_start = current_time
            meeting_end = get_meeting_end_time(person, meeting_start)
            meeting_location = meetings[person]['location']
            travel_to_meeting = travel_time(current_location, meeting_location)
            travel_back = travel_time(meeting_location, current_location)

            if current_time + travel_to_meeting + meeting_end - meeting_start + travel_back <= parse_time('23:59'):
                itinerary.append({
                    "action": "meet",
                    "location": meeting_location,
                    "person": person,
                    "start_time": time_to_str(meeting_start),
                    "end_time": time_to_str(meeting_end)
                })
                return meeting_end + travel_back, meeting_location
        return current_time, current_location

    # Try to meet Emily, Joseph, Melissa in order of their availability
    for person in ['Melissa', 'Emily', 'Joseph']:
        start_time, current_location = try_meeting(person, start_time, current_location)

    return itinerary

itinerary = find_meeting_schedule()
print(json.dumps({"itinerary": itinerary}))