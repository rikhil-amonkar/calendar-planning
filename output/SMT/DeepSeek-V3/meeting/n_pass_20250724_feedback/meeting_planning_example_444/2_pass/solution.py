from z3 import *
import datetime
import json

# Travel times in minutes between locations
travel_times = {
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('The Castro', 'Financial District'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
}

# Friends' availability and constraints
friends = {
    'Ronald': {
        'location': 'Russian Hill',
        'start': datetime.time(13, 45),  # 1:45 PM
        'end': datetime.time(17, 15),    # 5:15 PM
        'duration': 105,                 # minutes
    },
    'Patricia': {
        'location': 'Sunset District',
        'start': datetime.time(9, 15),   # 9:15 AM
        'end': datetime.time(22, 0),     # 10:00 PM
        'duration': 60,                  # minutes
    },
    'Laura': {
        'location': 'North Beach',
        'start': datetime.time(12, 30),  # 12:30 PM
        'end': datetime.time(12, 45),    # 12:45 PM
        'duration': 15,                  # minutes
    },
    'Emily': {
        'location': 'The Castro',
        'start': datetime.time(16, 15),  # 4:15 PM
        'end': datetime.time(18, 30),    # 6:30 PM
        'duration': 60,                  # minutes
    },
    'Mary': {
        'location': 'Golden Gate Park',
        'start': datetime.time(15, 0),   # 3:00 PM
        'end': datetime.time(16, 30),    # 4:30 PM
        'duration': 60,                  # minutes
    }
}

# Convert time to minutes since 9:00 AM (540 minutes)
def time_to_minutes(t):
    return t.hour * 60 + t.minute - 540  # 9:00 AM is 540 minutes

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting's start and end times
meetings = {}
for name in friends:
    start = Int(f'start_{name}')
    end = Int(f'end_{name}')
    meetings[name] = {'start': start, 'end': end, 'location': friends[name]['location']}
    # Constraints: start and end within friend's availability
    s.add(start >= time_to_minutes(friends[name]['start']))
    s.add(end <= time_to_minutes(friends[name]['end']))
    # Duration constraint
    s.add(end - start >= friends[name]['duration'])

# Initial location is Financial District at time 0 (9:00 AM)
current_location = 'Financial District'
current_time = 0

# Define the order of meetings as a permutation to explore all possibilities
# We'll use a list of all friends and let Z3 decide the order
all_friends = list(friends.keys())
order = [Int(f'order_{i}') for i in range(len(all_friends))]

# Ensure each order index is unique and within bounds
s.add(Distinct(order))
for o in order:
    s.add(o >= 0)
    s.add(o < len(all_friends))

# Add constraints for travel times between meetings
for i in range(len(all_friends)):
    if i == 0:
        # First meeting: travel from Financial District
        prev_location = current_location
        prev_time = current_time
    else:
        # Subsequent meetings: travel from previous meeting's location
        prev_idx = order[i-1]
        prev_name = all_friends[prev_idx]
        prev_location = meetings[prev_name]['location']
        prev_time = meetings[prev_name]['end']
    
    current_idx = order[i]
    current_name = all_friends[current_idx]
    current_meeting = meetings[current_name]
    travel_time = travel_times.get((prev_location, current_meeting['location']), 0)
    s.add(current_meeting['start'] >= prev_time + travel_time)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    # Extract the order of meetings
    meeting_order = sorted([(model[order[i]].as_long(), all_friends[i]) for i in range(len(all_friends))])
    meeting_order = [name for (_, name) in meeting_order]
    itinerary = []
    for name in meeting_order:
        start_val = model[meetings[name]['start']].as_long()
        end_val = model[meetings[name]['end']].as_long()
        start_time = (datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0)) + datetime.timedelta(minutes=start_val)).time()
        end_time = (datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0)) + datetime.timedelta(minutes=end_val)).time()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })
    print('SOLUTION:')
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found.")