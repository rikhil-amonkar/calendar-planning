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

# Convert time to minutes since midnight
def time_to_minutes(t):
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create variables for each meeting
meeting_vars = {}
for name in friends:
    start = Int(f'start_{name}')
    end = Int(f'end_{name}')
    meeting_vars[name] = {
        'start': start,
        'end': end,
        'location': friends[name]['location'],
        'available_start': time_to_minutes(friends[name]['start']),
        'available_end': time_to_minutes(friends[name]['end']),
        'duration': friends[name]['duration']
    }
    # Add basic constraints
    solver.add(start >= meeting_vars[name]['available_start'])
    solver.add(end <= meeting_vars[name]['available_end'])
    solver.add(end == start + meeting_vars[name]['duration'])

# Add arrival time constraint (9:00 AM = 540 minutes)
arrival_time = time_to_minutes(datetime.time(9, 0))

# Add constraints that all meetings must start after arrival time + travel time from Haight-Ashbury
for name in meeting_vars:
    travel_time = travel_times[('Haight-Ashbury', meeting_vars[name]['location'])]
    solver.add(meeting_vars[name]['start'] >= arrival_time + travel_time)

# Add travel time constraints between all meeting pairs
for name1 in friends:
    for name2 in friends:
        if name1 != name2:
            travel = travel_times[(meeting_vars[name1]['location'], 
                                 meeting_vars[name2]['location'])]
            solver.add(Or(
                meeting_vars[name2]['start'] >= meeting_vars[name1]['end'] + travel,
                meeting_vars[name1]['start'] >= meeting_vars[name2]['end'] + travel
            ))

# Try to find a solution
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for name in meeting_vars:
        start = model[meeting_vars[name]['start']].as_long()
        end = model[meeting_vars[name]['end']].as_long()
        schedule.append({
            'person': name,
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end),
            'location': meeting_vars[name]['location']
        })
    # Sort by start time
    schedule.sort(key=lambda x: x['start_time'])
    print('SOLUTION:')
    print({'itinerary': [
        {"action": "meet", "person": item['person'], 
         "start_time": item['start_time'], "end_time": item['end_time']}
        for item in schedule
    ]})
else:
    print("No valid schedule found that meets all constraints.")