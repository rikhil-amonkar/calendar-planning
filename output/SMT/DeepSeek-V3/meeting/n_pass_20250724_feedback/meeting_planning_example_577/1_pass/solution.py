from z3 import *
import datetime

# Define the travel times between locations
travel_times = {
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
}

# Define friends and their availability
friends = {
    'Stephanie': {
        'location': 'Russian Hill',
        'start': datetime.time(20, 0),
        'end': datetime.time(20, 45),
        'duration': 15,
    },
    'Kevin': {
        'location': 'Fisherman\'s Wharf',
        'start': datetime.time(19, 15),
        'end': datetime.time(21, 45),
        'duration': 75,
    },
    'Robert': {
        'location': 'Nob Hill',
        'start': datetime.time(7, 45),
        'end': datetime.time(10, 30),
        'duration': 90,
    },
    'Steven': {
        'location': 'Golden Gate Park',
        'start': datetime.time(8, 30),
        'end': datetime.time(17, 0),
        'duration': 75,
    },
    'Anthony': {
        'location': 'Alamo Square',
        'start': datetime.time(7, 45),
        'end': datetime.time(19, 45),
        'duration': 15,
    },
    'Sandra': {
        'location': 'Pacific Heights',
        'start': datetime.time(14, 45),
        'end': datetime.time(21, 45),
        'duration': 45,
    }
}

# Initialize Z3 solver
solver = Solver()

# Convert time to minutes since midnight for easier arithmetic
def time_to_minutes(t):
    return t.hour * 60 + t.minute

# Convert minutes back to time
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return datetime.time(hours, minutes)

# Define variables for each meeting's start and end times
meetings = {}
for name in friends:
    start_var = Int(f'start_{name}')
    end_var = Int(f'end_{name}')
    meetings[name] = {
        'start': start_var,
        'end': end_var,
        'location': friends[name]['location'],
        'duration': friends[name]['duration'],
        'available_start': time_to_minutes(friends[name]['start']),
        'available_end': time_to_minutes(friends[name]['end']),
    }
    # Add constraints for meeting within available time
    solver.add(start_var >= friends[name]['available_start'])
    solver.add(end_var <= friends[name]['available_end'])
    solver.add(end_var == start_var + friends[name]['duration'])

# Initial location is Haight-Ashbury at 9:00 AM (540 minutes)
current_location = 'Haight-Ashbury'
current_time = time_to_minutes(datetime.time(9, 0))

# Define the order of meetings (we'll try to meet all friends)
meeting_order = list(friends.keys())

# Add constraints for travel times between meetings
for i in range(len(meeting_order) - 1):
    current_meeting = meetings[meeting_order[i]]
    next_meeting = meetings[meeting_order[i + 1]]
    travel_time = travel_times[(current_meeting['location'], next_meeting['location'])]
    solver.add(next_meeting['start'] >= current_meeting['end'] + travel_time)

# Ensure the first meeting starts after arrival
first_meeting = meetings[meeting_order[0]]
solver.add(first_meeting['start'] >= current_time + travel_times[(current_location, first_meeting['location'])])

# Check if all meetings can be scheduled
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in meetings:
        start = model[meetings[name]['start']].as_long()
        end = model[meetings[name]['end']].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start).strftime("%H:%M"),
            "end_time": minutes_to_time(end).strftime("%H:%M")
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: datetime.datetime.strptime(x['start_time'], "%H:%M"))
    print('SOLUTION:')
    print({'itinerary': itinerary})
else:
    print("No valid schedule found.")