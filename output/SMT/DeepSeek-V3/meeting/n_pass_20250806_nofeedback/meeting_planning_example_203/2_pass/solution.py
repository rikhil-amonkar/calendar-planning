from z3 import *
import datetime

# Define the travel times between locations
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16,
}

# Define the friends' availability
friends = {
    'David': {
        'location': 'Fisherman\'s Wharf',
        'start': '10:45',
        'end': '15:30',
        'duration': 15,
    },
    'Timothy': {
        'location': 'Pacific Heights',
        'start': '09:00',
        'end': '15:30',
        'duration': 75,
    },
    'Robert': {
        'location': 'Mission District',
        'start': '12:15',
        'end': '19:45',
        'duration': 90,
    }
}

# Convert time strings to minutes since 9:00 AM (540 minutes)
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m - 540  # 9:00 AM is 540 minutes

# Convert minutes back to time string
def minutes_to_time(minutes):
    total_minutes = 540 + minutes
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Initialize Z3 solver
solver = Solver()

# Create variables for each meeting's start and end times
meetings = {}
for name in friends:
    meetings[name] = {
        'start': Int(f'start_{name}'),
        'end': Int(f'end_{name}'),
        'location': friends[name]['location'],
        'duration': friends[name]['duration'],
        'available_start': time_to_minutes(friends[name]['start']),
        'available_end': time_to_minutes(friends[name]['end']),
    }

# Add constraints for each meeting
for name in meetings:
    m = meetings[name]
    solver.add(m['start'] >= m['available_start'])
    solver.add(m['end'] <= m['available_end'])
    solver.add(m['end'] == m['start'] + m['duration'])

# Add constraints for travel times between meetings
# We'll consider all possible permutations of meeting orders
from itertools import permutations

# Try all possible meeting orders
for order in permutations(['Timothy', 'David', 'Robert']):
    temp_solver = Solver()
    for name in meetings:
        m = meetings[name]
        temp_solver.add(m['start'] >= m['available_start'])
        temp_solver.add(m['end'] <= m['available_end'])
        temp_solver.add(m['end'] == m['start'] + m['duration'])

    # Start at Financial District at 9:00 AM (0 minutes)
    current_location = 'Financial District'
    current_time = 0

    for name in order:
        m = meetings[name]
        temp_solver.add(m['start'] >= current_time + travel_times[(current_location, m['location'])])
        current_location = m['location']
        current_time = m['end']

    if temp_solver.check() == sat:
        model = temp_solver.model()
        itinerary = []
        for name in meetings:
            start = model[meetings[name]['start']].as_long()
            end = model[meetings[name]['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end),
            })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        print({'itinerary': itinerary})
        break
else:
    print("No solution found")