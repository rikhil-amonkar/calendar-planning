from z3 import *
import json

# Travel times dictionary
travel_dict = {
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
    ('Bayview', 'Nob Hill'): 20
}

# Meetings data
meetings = [
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start_avail': 8*60, 'end_avail': 11*60+30, 'duration': 90},
    {'name': 'Andrew', 'location': 'Nob Hill', 'start_avail': 11*60+30, 'end_avail': 20*60+15, 'duration': 60},
    {'name': 'Joshua', 'location': 'Financial District', 'start_avail': 12*60, 'end_avail': 15*60+15, 'duration': 15},
    {'name': 'Lisa', 'location': 'Union Square', 'start_avail': 9*60, 'end_avail': 16*60+30, 'duration': 45},
    {'name': 'John', 'location': 'Bayview', 'start_avail': 16*60+45, 'end_avail': 21*60+30, 'duration': 75},
    {'name': 'Kenneth', 'location': 'Richmond District', 'start_avail': 21*60+15, 'end_avail': 22*60, 'duration': 30}
]

n = len(meetings)
s = Solver()

# Create variables for each meeting: a boolean flag and a start time (in minutes)
meet_flags = [Bool(f"meet_{i}") for i in range(n)]
start_times = [Int(f"start_{i}") for i in range(n)]

# Constraint: For each meeting, if scheduled, it must start after traveling from Embarcadero and within availability window
for i in range(n):
    loc = meetings[i]['location']
    travel_time = travel_dict[('Embarcadero', loc)]
    s.add(Implies(meet_flags[i], start_times[i] >= 540 + travel_time))  # 540 = 9:00 AM in minutes
    s.add(Implies(meet_flags[i], start_times[i] >= meetings[i]['start_avail']))
    s.add(Implies(meet_flags[i], start_times[i] + meetings[i]['duration'] <= meetings[i]['end_avail']))

# Constraint: For every pair of meetings, if both are scheduled, they must not overlap and account for travel time
for i in range(n):
    for j in range(i+1, n):
        if i != j:
            loc_i = meetings[i]['location']
            loc_j = meetings[j]['location']
            travel_ij = travel_dict[(loc_i, loc_j)]
            travel_ji = travel_dict[(loc_j, loc_i)]
            constraint = Or(
                start_times[i] + meetings[i]['duration'] + travel_ij <= start_times[j],
                start_times[j] + meetings[j]['duration'] + travel_ji <= start_times[i]
            )
            s.add(Implies(And(meet_flags[i], meet_flags[j]), constraint))

# Objective: Maximize the number of meetings
opt = Optimize()
for c in s.assertions():
    opt.add(c)
num_meetings = Sum([If(meet_flags[i], 1, 0) for i in range(n)])
opt.maximize(num_meetings)

if opt.check() == sat:
    m = opt.model()
    scheduled_meetings = []
    for i in range(n):
        if is_true(m.eval(meet_flags[i])):
            start_val = m.eval(start_times[i])
            if is_int_value(start_val):
                start_minutes = start_val.as_long()
                end_minutes = start_minutes + meetings[i]['duration']
                # Format start and end times
                start_hour = start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = end_minutes // 60
                end_minute = end_minutes % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                scheduled_meetings.append({
                    "action": "meet",
                    "person": meetings[i]['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
    # Sort by start time
    scheduled_meetings.sort(key=lambda x: x['start_time'])
    result = {"itinerary": scheduled_meetings}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")