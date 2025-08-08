from z3 import *
import datetime

# Define the travel times between locations
travel_times = {
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Bayview'): 21,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Bayview'): 26,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Bayview'): 15,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Bayview'): 19,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Bayview'): 22,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Bayview'): 19,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Nob Hill'): 20,
}

# Define friends and their availability
friends = [
    {
        'name': 'Kenneth',
        'location': 'Richmond District',
        'start': datetime.time(21, 15),  # 9:15 PM
        'end': datetime.time(22, 0),     # 10:00 PM
        'duration': 30,                  # minutes
    },
    {
        'name': 'Lisa',
        'location': 'Union Square',
        'start': datetime.time(9, 0),   # 9:00 AM
        'end': datetime.time(16, 30),    # 4:30 PM
        'duration': 45,                  # minutes
    },
    {
        'name': 'Joshua',
        'location': 'Financial District',
        'start': datetime.time(12, 0),  # 12:00 PM
        'end': datetime.time(15, 15),   # 3:15 PM
        'duration': 15,                 # minutes
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'start': datetime.time(8, 0),   # 8:00 AM
        'end': datetime.time(11, 30),   # 11:30 AM
        'duration': 90,                  # minutes
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'start': datetime.time(11, 30),  # 11:30 AM
        'end': datetime.time(20, 15),    # 8:15 PM
        'duration': 60,                 # minutes
    },
    {
        'name': 'John',
        'location': 'Bayview',
        'start': datetime.time(16, 45), # 4:45 PM
        'end': datetime.time(21, 30),    # 9:30 PM
        'duration': 75,                  # minutes
    },
]

# Initialize Z3 solver
solver = Solver()

# Convert time to minutes since 9:00 AM (540 minutes)
def time_to_minutes(t):
    return t.hour * 60 + t.minute - 540  # 9:00 AM is 540 minutes

# Variables for each meeting: start time and whether it's scheduled
meetings = []
for friend in friends:
    start = Int(f'start_{friend["name"]}')
    scheduled = Bool(f'scheduled_{friend["name"]}')
    meetings.append({
        'name': friend['name'],
        'location': friend['location'],
        'start_var': start,
        'scheduled_var': scheduled,
        'duration': friend['duration'],
        'availability_start': time_to_minutes(friend['start']),
        'availability_end': time_to_minutes(friend['end']),
    })

# Constraints for each meeting
for meeting in meetings:
    # If scheduled, start time must be within availability
    solver.add(Implies(meeting['scheduled_var'], 
                   And(meeting['start_var'] >= meeting['availability_start'],
                       meeting['start_var'] + meeting['duration'] <= meeting['availability_end'])))
    # If not scheduled, start time is -1
    solver.add(Implies(Not(meeting['scheduled_var']), meeting['start_var'] == -1)

# Order constraints (ensure no overlaps considering travel time)
for i in range(len(meetings)):
    for j in range(i + 1, len(meetings)):
        # Only consider if both are scheduled
        both_scheduled = And(meetings[i]['scheduled_var'], meetings[j]['scheduled_var'])
        # Either i before j or j before i, with travel time
        travel_ij = travel_times.get((meetings[i]['location'], meetings[j]['location']), 0)
        travel_ji = travel_times.get((meetings[j]['location'], meetings[i]['location']), 0)
        solver.add(Implies(both_scheduled,
                         Or(meetings[i]['start_var'] + meetings[i]['duration'] + travel_ij <= meetings[j]['start_var'],
                            meetings[j]['start_var'] + meetings[j]['duration'] + travel_ji <= meetings[i]['start_var'])))

# Maximize the number of friends met
solver.maximize(Sum([If(m['scheduled_var'], 1, 0) for m in meetings]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for meeting in meetings:
        if is_true(model[meeting['scheduled_var']]):
            start_min = model[meeting['start_var']].as_long()
            start_time = datetime.time(9 + (start_min // 60), start_min % 60)
            end_time = datetime.time(9 + ((start_min + meeting['duration']) // 60), 
                                     (start_min + meeting['duration']) % 60)
            itinerary.append({
                'action': 'meet',
                'person': meeting['name'],
                'start_time': start_time.strftime('%H:%M'),
                'end_time': end_time.strftime('%H:%M')
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print({'itinerary': itinerary})
else:
    print("No solution found")