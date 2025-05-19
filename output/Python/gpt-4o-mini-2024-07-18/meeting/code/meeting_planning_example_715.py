import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
}

# Meeting constraints
meetings = {
    'Amanda': {'location': 'Marina District', 'start': '14:45', 'end': '19:30', 'duration': 105},
    'Melissa': {'location': 'The Castro', 'start': '09:30', 'end': '17:00', 'duration': 30},
    'Jeffrey': {'location': 'Fisherman\'s Wharf', 'start': '12:45', 'end': '18:45', 'duration': 120},
    'Matthew': {'location': 'Bayview', 'start': '10:15', 'end': '13:15', 'duration': 30},
    'Nancy': {'location': 'Pacific Heights', 'start': '17:00', 'end': '21:30', 'duration': 105},
    'Karen': {'location': 'Mission District', 'start': '17:30', 'end': '20:30', 'duration': 105},
    'Robert': {'location': 'Alamo Square', 'start': '11:15', 'end': '17:30', 'duration': 120},
    'Joseph': {'location': 'Golden Gate Park', 'start': '08:30', 'end': '21:15', 'duration': 105},
}

# Convert string time to datetime object
def str_to_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Check if a meeting can occur between two time periods and includes travel time
def can_meet(start_a, end_a, start_b, end_b, travel_time):
    return not (end_a + timedelta(minutes=travel_time) > start_b or end_b < start_a)

# Planning the itinerary
itinerary = []
current_time = str_to_time('09:00')  # starting at Presidio
current_location = 'Presidio'

while True:
    if current_location == 'Marina District':
        person = 'Amanda'
    elif current_location == 'The Castro':
        person = 'Melissa'
    elif current_location == 'Fisherman\'s Wharf':
        person = 'Jeffrey'
    elif current_location == 'Bayview':
        person = 'Matthew'
    elif current_location == 'Pacific Heights':
        person = 'Nancy'
    elif current_location == 'Mission District':
        person = 'Karen'
    elif current_location == 'Alamo Square':
        person = 'Robert'
    elif current_location == 'Golden Gate Park':
        person = 'Joseph'
    else:
        break
    
    meeting_info = meetings[person]
    meeting_start = str_to_time(meeting_info['start'])
    meeting_end = str_to_time(meeting_info['end'])

    if current_time < meeting_start:
        current_time = meeting_start

    # If we can meet
    if can_meet(current_time, meeting_end, meeting_start, meeting_end, travel_times[(current_location, meeting_info['location'])]):
        duration = meeting_info['duration']
        end_meeting_time = current_time + timedelta(minutes=duration)

        # Schedule the meeting
        itinerary.append({
            "action": "meet",
            "location": meeting_info['location'],
            "person": person,
            "start_time": current_time.strftime('%H:%M'),
            "end_time": end_meeting_time.strftime('%H:%M')
        })

        current_time = end_meeting_time + timedelta(minutes=travel_times[(current_location, meeting_info['location'])])
        current_location = meeting_info['location']
        
        # Remove the meeting from the list (to not meet twice)
        del meetings[person]
    else:
        # Move to the next meeting in a location where currently not scheduled
        if not meetings:
            break
        
        # Sort and choose the closest location we can still meet
        next_location = min(meetings.items(), key=lambda x: travel_times[(current_location, x[1]['location'])])[1]
        travel_time = travel_times[(current_location, next_location['location'])]
        current_time += timedelta(minutes=travel_time)
        current_location = next_location['location']
        
# Output JSON
output = json.dumps({"itinerary": itinerary}, indent=2)
print(output)