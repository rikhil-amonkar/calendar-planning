from z3 import *

def min_to_time(total_minutes):
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

travel_text = """
Union Square to The Castro: 17.
Union Square to North Beach: 10.
Union Square to Embarcadero: 11.
Union Square to Alamo Square: 15.
Union Square to Nob Hill: 9.
Union Square to Presidio: 24.
Union Square to Fisherman's Wharf: 15.
Union Square to Mission District: 14.
Union Square to Haight-Ashbury: 18.
The Castro to Union Square: 19.
The Castro to North Beach: 20.
The Castro to Embarcadero: 22.
The Castro to Alamo Square: 8.
The Castro to Nob Hill: 16.
The Castro to Presidio: 20.
The Castro to Fisherman's Wharf: 24.
The Castro to Mission District: 7.
The Castro to Haight-Ashbury: 6.
North Beach to Union Square: 7.
North Beach to The Castro: 23.
North Beach to Embarcadero: 6.
North Beach to Alamo Square: 16.
North Beach to Nob Hill: 7.
North Beach to Presidio: 17.
North Beach to Fisherman's Wharf: 5.
North Beach to Mission District: 18.
North Beach to Haight-Ashbury: 18.
Embarcadero to Union Square: 10.
Embarcadero to The Castro: 25.
Embarcadero to North Beach: 5.
Embarcadero to Alamo Square: 19.
Embarcadero to Nob Hill: 10.
Embarcadero to Presidio: 20.
Embarcadero to Fisherman's Wharf: 6.
Embarcadero to Mission District: 20.
Embarcadero to Haight-Ashbury: 21.
Alamo Square to Union Square: 14.
Alamo Square to The Castro: 8.
Alamo Square to North Beach: 15.
Alamo Square to Embarcadero: 16.
Alamo Square to Nob Hill: 11.
Alamo Square to Presidio: 17.
Alamo Square to Fisherman's Wharf: 19.
Alamo Square to Mission District: 10.
Alamo Square to Haight-Ashbury: 5.
Nob Hill to Union Square: 7.
Nob Hill to The Castro: 17.
Nob Hill to North Beach: 8.
Nob Hill to Embarcadero: 9.
Nob Hill to Alamo Square: 11.
Nob Hill to Presidio: 17.
Nob Hill to Fisherman's Wharf: 10.
Nob Hill to Mission District: 13.
Nob Hill to Haight-Ashbury: 13.
Presidio to Union Square: 22.
Presidio to The Castro: 21.
Presidio to North Beach: 18.
Presidio to Embarcadero: 20.
Presidio to Alamo Square: 19.
Presidio to Nob Hill: 18.
Presidio to Fisherman's Wharf: 19.
Presidio to Mission District: 26.
Presidio to Haight-Ashbury: 15.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to The Castro: 27.
Fisherman's Wharf to North Beach: 6.
Fisherman's Wharf to Embarcadero: 8.
Fisherman's Wharf to Alamo Square: 21.
Fisherman's Wharf to Nob Hill: 11.
Fisherman's Wharf to Presidio: 17.
Fisherman's Wharf to Mission District: 22.
Fisherman's Wharf to Haight-Ashbury: 22.
Mission District to Union Square: 15.
Mission District to The Castro: 7.
Mission District to North Beach: 17.
Mission District to Embarcadero: 19.
Mission District to Alamo Square: 11.
Mission District to Nob Hill: 12.
Mission District to Presidio: 25.
Mission District to Fisherman's Wharf: 22.
Mission District to Haight-Ashbury: 12.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Mission District: 11.
"""

travel_time_dict = {}
lines = travel_text.strip().split('\n')
for line in lines:
    if line:
        parts = line.split(':')
        locations_str = parts[0].strip()
        time_str = parts[1].strip().rstrip('.')
        from_loc, to_loc = locations_str.split(' to ')
        travel_time_dict[(from_loc, to_loc)] = int(time_str)

friends = [
    {"name": "Melissa", "location": "The Castro", "window_start": 675, "window_end": 735, "min_duration": 30},
    {"name": "Kimberly", "location": "North Beach", "window_start": 0, "window_end": 90, "min_duration": 15},
    {"name": "Joseph", "location": "Embarcadero", "window_start": 390, "window_end": 630, "min_duration": 75},
    {"name": "Barbara", "location": "Alamo Square", "window_start": 705, "window_end": 765, "min_duration": 15},
    {"name": "Kenneth", "location": "Nob Hill", "window_start": 195, "window_end": 495, "min_duration": 105},
    {"name": "Joshua", "location": "Presidio", "window_start": 450, "window_end": 555, "min_duration": 105},
    {"name": "Brian", "location": "Fisherman's Wharf", "window_start": 30, "window_end": 390, "min_duration": 45},
    {"name": "Steven", "location": "Mission District", "window_start": 630, "window_end": 720, "min_duration": 90},
    {"name": "Betty", "location": "Haight-Ashbury", "window_start": 600, "window_end": 690, "min_duration": 90}
]

s = Optimize()

n_friends = len(friends)
n_nodes = n_friends + 2

selected = [Bool(f"selected_{i}") for i in range(1, n_friends+1)]
next_var = [Int(f"next_{i}") for i in range(n_nodes-1)]
s_time = [Int(f"s_{i}") for i in range(n_nodes)]
e_time = [Int(f"e_{i}") for i in range(n_nodes)]
rank = [Int(f"rank_{i}") for i in range(n_nodes)]

locations = ["Union Square"] + [f['location'] for f in friends] + ["Dummy_End"]

for i in range(n_nodes-1):
    s.add(And(next_var[i] >= 1, next_var[i] <= n_nodes-1))

s.add(s_time[0] == 0)
s.add(e_time[0] == 0)
s.add(rank[0] == 0)

total_selected = Sum([If(selected[i], 1, 0) for i in range(n_friends)])

s.add(If(total_selected == 0, next_var[0] == n_nodes-1, 
         Or([And(selected[i], next_var[0] == i+1) for i in range(n_friends)])))

for i in range(1, n_friends+1):
    s.add(Implies(selected[i-1], 
                 And(s_time[i] >= friends[i-1]['window_start'],
                     e_time[i] == s_time[i] + friends[i-1]['min_duration'],
                     e_time[i] <= friends[i-1]['window_end'])))
    s.add(Implies(Not(selected[i-1]), 
                 And(s_time[i] == -1, e_time[i] == -1)))

for i in range(1, n_friends+1):
    incoming = [next_var[j] == i for j in range(n_nodes-1)]
    s.add(Implies(selected[i-1], Sum([If(cond, 1, 0) for cond in incoming]) == 1))
    s.add(Implies(Not(selected[i-1]), Sum([If(cond, 1, 0) for cond in incoming]) == 0))

for i in range(1, n_friends+1):
    s.add(Implies(selected[i-1],
                  Or([And(selected[j-1], next_var[i] == j) for j in range(1, n_friends+1) if j != i] + 
                     [next_var[i] == n_nodes-1])))

for i in range(n_friends+1, n_nodes):
    s.add(rank[i] == -1)

for i in range(n_nodes-1):
    for j in range(1, n_nodes):
        s.add(Implies(next_var[i] == j, rank[j] == rank[i] + 1))

for i in range(n_nodes-1):
    for j in range(1, n_friends+1):
        if i == 0:
            cond = (next_var[i] == j)
        else:
            cond = And(selected[i-1], next_var[i] == j)
        loc_i = locations[i]
        loc_j = locations[j]
        travel_time = travel_time_dict.get((loc_i, loc_j), 0)
        s.add(Implies(cond, s_time[j] >= e_time[i] + travel_time))

s.maximize(total_selected)

if s.check() == sat:
    model = s.model()
    scheduled_meetings = []
    for i in range(n_friends):
        if is_true(model.eval(selected[i])):
            start_val = model.eval(s_time[i+1]).as_long()
            end_val = model.eval(e_time[i+1]).as_long()
            start_time_str = min_to_time(start_val)
            end_time_str = min_to_time(end_val)
            scheduled_meetings.append({
                "action": "meet",
                "person": friends[i]['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    scheduled_meetings.sort(key=lambda x: x['start_time'])
    print('SOLUTION:')
    print(f'{{"itinerary": {scheduled_meetings}}}')
else:
    print("No solution found")