from z3 import *
import json

# Define the travel times between locations
travel_times = {
    'Pacific Heights': {
        'Golden Gate Park': 15,
        'The Castro': 16,
        'Bayview': 22,
        'Marina District': 6,
        'Union Square': 12,
        'Sunset District': 21,
        'Alamo Square': 10,
        'Financial District': 13,
        'Mission District': 15
    },
    'Golden Gate Park': {
        'Pacific Heights': 16,
        'The Castro': 13,
        'Bayview': 23,
        'Marina District': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'Mission District': 17
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Bayview': 19,
        'Marina District': 21,
        'Union Square': 19,
        'Sunset District': 17,
        'Alamo Square': 8,
        'Financial District': 21,
        'Mission District': 7
    },
    'Bayview': {
        'Pacific Heights': 23,
        'Golden Gate Park': 22,
        'The Castro': 19,
        'Marina District': 27,
        'Union Square': 18,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'Mission District': 13
    },
    'Marina District': {
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'The Castro': 22,
        'Bayview': 27,
        'Union Square': 16,
        'Sunset District': 19,
        'Alamo Square': 15,
        'Financial District': 17,
        'Mission District': 20
    },
    'Union Square': {
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'The Castro': 17,
        'Bayview': 15,
        'Marina District': 18,
        'Sunset District': 27,
        'Alamo Square': 15,
        'Financial District': 9,
        'Mission District': 14
    },
    'Sunset District': {
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'The Castro': 17,
        'Bayview': 22,
        'Marina District': 21,
        'Union Square': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'Mission District': 25
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'The Castro': 8,
        'Bayview': 16,
        'Marina District': 15,
        'Union Square': 14,
        'Sunset District': 16,
        'Financial District': 17,
        'Mission District': 10
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
        'The Castro': 20,
        'Bayview': 19,
        'Marina District': 15,
        'Union Square': 9,
        'Sunset District': 30,
        'Alamo Square': 17,
        'Mission District': 17
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'The Castro': 7,
        'Bayview': 14,
        'Marina District': 19,
        'Union Square': 15,
        'Sunset District': 24,
        'Alamo Square': 11,
        'Financial District': 15
    }
}

# Define the friends' availability and constraints
friends = [
    {
        'name': 'Helen',
        'location': 'Golden Gate Park',
        'start': (9, 30),
        'end': (12, 15),
        'duration': 45
    },
    {
        'name': 'Steven',
        'location': 'The Castro',
        'start': (20, 15),
        'end': (22, 0),
        'duration': 105
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'start': (8, 30),
        'end': (12, 0),
        'duration': 30
    },
    {
        'name': 'Matthew',
        'location': 'Marina District',
        'start': (9, 15),
        'end': (14, 15),
        'duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Union Square',
        'start': (14, 15),
        'end': (18, 45),
        'duration': 120
    },
    {
        'name': 'Ronald',
        'location': 'Sunset District',
        'start': (16, 0),
        'end': (20, 45),
        'duration': 60
    },
    {
        'name': 'Robert',
        'location': 'Alamo Square',
        'start': (18, 30),
        'end': (21, 15),
        'duration': 120
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'start': (14, 45),
        'end': (16, 15),
        'duration': 30
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'start': (18, 30),
        'end': (21, 0),
        'duration': 120
    }
]

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting's start and end times
meetings = {}
for friend in friends:
    name = friend['name']
    meetings[name] = {
        'start': Int(f'start_{name}'),
        'end': Int(f'end_{name}'),
        'location': friend['location'],
        'duration': friend['duration'],
        'available_start': friend['start'][0] * 60 + friend['start'][1],
        'available_end': friend['end'][0] * 60 + friend['end'][1]
    }

# Add constraints for each meeting
for name, meeting in meetings.items():
    s.add(meeting['start'] >= meeting['available_start'])
    s.add(meeting['end'] <= meeting['available_end'])
    s.add(meeting['end'] == meeting['start'] + meeting['duration'])

# Add constraints for travel times between consecutive meetings
meeting_names = list(meetings.keys())
for i in range(len(meeting_names)):
    for j in range(len(meeting_names)):
        if i != j:
            m1 = meeting_names[i]
            m2 = meeting_names[j]
            loc1 = meetings[m1]['location']
            loc2 = meetings[m2]['location']
            travel_time = travel_times.get(loc1, {}).get(loc2, 0)
            s.add(Implies(meetings[m1]['end'] <= meetings[m2]['start'],
                          meetings[m2]['start'] >= meetings[m1]['end'] + travel_time))

# Add constraint that the first meeting must start after 9:00 AM (540 minutes) plus travel time
# Create a variable to track the earliest start time
earliest_start = Int('earliest_start')
s.add(earliest_start >= 540)  # 9:00 AM in minutes

# For each meeting, if it's the first one, its start time must be >= 540 + travel time from Pacific Heights
for name in meeting_names:
    travel_time = travel_times['Pacific Heights'][meetings[name]['location']]
    s.add(Implies(meetings[name]['start'] == earliest_start,
                  meetings[name]['start'] >= 540 + travel_time))

# Ensure earliest_start is indeed the earliest start time
for name in meeting_names:
    s.add(earliest_start <= meetings[name]['start'])

# The solver will find a feasible schedule
if s.check() == sat:
    model = s.model()
    itinerary = []
    for name, meeting in meetings.items():
        start = model[meeting['start']].as_long()
        end = model[meeting['end']].as_long()
        start_hour = start // 60
        start_minute = start % 60
        end_hour = end // 60
        end_minute = end % 60
        itinerary.append({
            'action': 'meet',
            'person': name,
            'start_time': f"{start_hour:02d}:{start_minute:02d}",
            'end_time': f"{end_hour:02d}:{end_minute:02d}"
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
    print(json.dumps({'itinerary': itinerary}, indent=4))
else:
    print('No feasible schedule found.')