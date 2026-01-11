import json
from datetime import datetime, timedelta

# Constants
START_TIME = 9 * 60  # 9:00 AM in minutes
TRAVEL_TIMES = {
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Financial District'): 20,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Financial District'): 17,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Mission District'): 17,
}

# Friends' availability and minimum meet times
FRIENDS = {
    'Laura': {
        'location': 'Mission District',
        'start': 12 * 60 + 15,  # 12:15 PM
        'end': 19 * 60 + 45,    # 7:45 PM
        'min_meet_time': 75
    },
    'Anthony': {
        'location': 'Financial District',
        'start': 12 * 60 + 30,  # 12:30 PM
        'end': 14 * 60 + 45,    # 2:45 PM
        'min_meet_time': 30
    }
}

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def find_optimal_schedule():
    current_time = START_TIME
    itinerary = []

    def can_meet(friend, current_time):
        travel_time = TRAVEL_TIMES[(current_location, friend['location'])]
        meet_start = max(current_time + travel_time, friend['start'])
        meet_end = min(meet_start + friend['min_meet_time'], friend['end'])
        return meet_start + friend['min_meet_time'] <= meet_end

    def add_meeting(friend, current_time):
        travel_time = TRAVEL_TIMES[(current_location, friend['location'])]
        meet_start = max(current_time + travel_time, friend['start'])
        meet_end = meet_start + friend['min_meet_time']
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": convert_minutes_to_time(meet_start),
            "end_time": convert_minutes_to_time(meet_end)
        })
        return meet_end

    current_location = 'The Castro'
    for friend_name, friend in FRIENDS.items():
        friend['name'] = friend_name
        if can_meet(friend, current_time):
            current_time = add_meeting(friend, current_time)
            current_location = friend['location']

    return itinerary

itinerary = find_optimal_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))