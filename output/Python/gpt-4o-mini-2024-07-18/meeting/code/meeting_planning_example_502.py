import json
from datetime import datetime, timedelta
from itertools import permutations

# Travel times in minutes
travel_times = {
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'North Beach'): 3,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Pacific Heights', 'North Beach'): 8,
}

# Meeting constraints and times
meetings = {
    "Stephanie": {
        "location": "Golden Gate Park",
        "start": "11:00",
        "end": "15:00",
        "duration": 105,
    },
    "Karen": {
        "location": "Chinatown",
        "start": "13:45",
        "end": "16:30",
        "duration": 15,
    },
    "Brian": {
        "location": "Union Square",
        "start": "15:00",
        "end": "17:15",
        "duration": 30,
    },
    "Rebecca": {
        "location": "Fisherman's Wharf",
        "start": "08:00",
        "end": "11:15",
        "duration": 30,
    },
    "Joseph": {
        "location": "Pacific Heights",
        "start": "08:15",
        "end": "09:30",
        "duration": 60,
    },
    "Steven": {
        "location": "North Beach",
        "start": "14:30",
        "end": "20:45",
        "duration": 120,
    },
}

start_time = datetime.strptime("09:00", "%H:%M")
itinerary = []
current_time = start_time
current_location = 'Financial District'

def can_meet(current_time, current_location, person):
    travel_time = travel_times.get((current_location, person['location']))
    if travel_time is None:
        return False
    
    arrival_time = current_time + timedelta(minutes=travel_time)
    start_time = datetime.strptime(person['start'], "%H:%M")
    end_time = datetime.strptime(person['end'], "%H:%M")

    if arrival_time < start_time:
        # Wait until meeting starts
        arrival_time = start_time
    
    meeting_end_time = arrival_time + timedelta(minutes=person['duration'])

    # Check if the meeting can fit in the available time
    return arrival_time <= end_time and meeting_end_time <= end_time

def schedule_meeting(current_time, current_location, person):
    travel_time = travel_times[(current_location, person['location'])]
    arrival_time = current_time + timedelta(minutes=travel_time)
    start_meeting_time = max(arrival_time, datetime.strptime(person['start'], "%H:%M"))
    end_meeting_time = start_meeting_time + timedelta(minutes=person['duration'])
    
    return start_meeting_time, end_meeting_time

# Visit friends based on their available times
def visit_friends():
    global current_time, current_location
    for friend in meetings:
        person = meetings[friend]
        if can_meet(current_time, current_location, person):
            start_meeting_time, end_meeting_time = schedule_meeting(current_time, current_location, person)
            itinerary.append({
                "action": "meet",
                "location": person['location'],
                "person": friend,
                "start_time": start_meeting_time.strftime("%H:%M"),
                "end_time": end_meeting_time.strftime("%H:%M"),
            })
            # Update the current time and location
            current_time = end_meeting_time
            current_location = person['location']

visit_friends()

print(json.dumps({"itinerary": itinerary}, indent=2))