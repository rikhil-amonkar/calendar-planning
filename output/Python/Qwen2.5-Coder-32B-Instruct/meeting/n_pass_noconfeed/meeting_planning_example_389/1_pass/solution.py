import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 13,
}

# Define meeting constraints
meetings = {
    'Sarah': {'location': 'Fisherman\'s Wharf', 'start': '14:45', 'end': '17:30', 'min_duration': 105},
    'Mary': {'location': 'Richmond District', 'start': '13:00', 'end': '19:15', 'min_duration': 75},
    'Helen': {'location': 'Mission District', 'start': '21:45', 'end': '22:30', 'min_duration': 30},
    'Thomas': {'location': 'Bayview', 'start': '15:15', 'end': '18:45', 'min_duration': 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M')

def find_meeting_schedule():
    start_time = parse_time('9:00')
    current_location = 'Haight-Ashbury'
    itinerary = []

    def can_meet(meeting, current_time):
        meeting_start = parse_time(meeting['start'])
        meeting_end = parse_time(meeting['end'])
        return meeting_start <= current_time + timedelta(minutes=meeting['min_duration']) <= meeting_end

    def travel_to(location, current_time, current_location):
        travel_time = travel_times[(current_location, location)]
        return current_time + timedelta(minutes=travel_time)

    # Sort meetings by earliest possible start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for name, meeting in sorted_meetings:
        while True:
            travel_time = travel_to(meeting['location'], start_time, current_location)
            if can_meet(meeting, travel_time):
                meet_start = max(travel_time, parse_time(meeting['start']))
                meet_end = meet_start + timedelta(minutes=meeting['min_duration'])
                itinerary.append({
                    "action": "meet",
                    "location": meeting['location'],
                    "person": name,
                    "start_time": format_time(meet_start),
                    "end_time": format_time(meet_end)
                })
                start_time = meet_end
                current_location = meeting['location']
                break
            else:
                # If we can't meet now, try to move to the next possible meeting time
                start_time += timedelta(minutes=1)
                if start_time >= parse_time(meeting['end']):
                    break

    return {"itinerary": itinerary}

SOLUTION = find_meeting_schedule()
print(json.dumps(SOLUTION))