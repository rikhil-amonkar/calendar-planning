import json
from z3 import *

# Travel times data as a multi-line string
travel_data = """
Russian Hill to Marina District: 7.
Russian Hill to Financial District: 11.
Russian Hill to Alamo Square: 15.
Russian Hill to Golden Gate Park: 21.
Russian Hill to The Castro: 21.
Russian Hill to Bayview: 23.
Russian Hill to Sunset District: 23.
Russian Hill to Haight-Ashbury: 17.
Russian Hill to Nob Hill: 5.
Marina District to Russian Hill: 8.
Marina District to Financial District: 17.
Marina District to Alamo Square: 15.
Marina District to Golden Gate Park: 18.
Marina District to The Castro: 22.
Marina District to Bayview: 27.
Marina District to Sunset District: 19.
Marina District to Haight-Ashbury: 16.
Marina District to Nob Hill: 12.
Financial District to Russian Hill: 11.
Financial District to Marina District: 15.
Financial District to Alamo Square: 17.
Financial District to Golden Gate Park: 23.
Financial District to The Castro: 20.
Financial District to Bayview: 19.
Financial District to Sunset District: 30.
Financial District to Haight-Ashbury: 19.
Financial District to Nob Hill: 8.
Alamo Square to Russian Hill: 13.
Alamo Square to Marina District: 15.
Alamo Square to Financial District: 17.
Alamo Square to Golden Gate Park: 9.
Alamo Square to The Castro: 8.
Alamo Square to Bayview: 16.
Alamo Square to Sunset District: 16.
Alamo Square to Haight-Ashbury: 5.
Alamo Square to Nob Hill: 11.
Golden Gate Park to Russian Hill: 19.
Golden Gate Park to Marina District: 16.
Golden Gate Park to Financial District: 26.
Golden Gate Park to Alamo Square: 9.
Golden Gate Park to The Castro: 13.
Golden Gate Park to Bayview: 23.
Golden Gate Park to Sunset District: 10.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Nob Hill: 20.
The Castro to Russian Hill: 18.
The Castro to Marina District: 21.
The Castro to Financial District: 21.
The Castro to Alamo Square: 8.
The Castro to Golden Gate Park: 11.
The Castro to Bayview: 19.
The Castro to Sunset District: 17.
The Castro to Haight-Ashbury: 6.
The Castro to Nob Hill: 16.
Bayview to Russian Hill: 23.
Bayview to Marina District: 27.
Bayview to Financial District: 19.
Bayview to Alamo Square: 16.
Bayview to Golden Gate Park: 22.
Bayview to The Castro: 19.
Bayview to Sunset District: 23.
Bayview to Haight-Ashbury: 19.
Bayview to Nob Hill: 20.
Sunset District to Russian Hill: 24.
Sunset District to Marina District: 21.
Sunset District to Financial District: 30.
Sunset District to Alamo Square: 17.
Sunset District to Golden Gate Park: 11.
Sunset District to The Castro: 17.
Sunset District to Bayview: 22.
Sunset District to Haight-Ashbury: 15.
Sunset District to Nob Hill: 27.
Haight-Ashbury to Russian Hill: 17.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Financial District: 21.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to Sunset District: 15.
Haight-Ashbury to Nob Hill: 15.
Nob Hill to Russian Hill: 5.
Nob Hill to Marina District: 11.
Nob Hill to Financial District: 9.
Nob Hill to Alamo Square: 11.
Nob Hill to Golden Gate Park: 17.
Nob Hill to The Castro: 17.
Nob Hill to Bayview: 19.
Nob Hill to Sunset District: 24.
Nob Hill to Haight-Ashbury: 13.
"""

# Build travel_times dictionary
travel_times = {}
lines = travel_data.strip().split('\n')
for line in lines:
    if line.endswith('.'):
        line = line[:-1]
    parts = line.split(':')
    if len(parts) < 2:
        continue
    time_val = int(parts[1].strip())
    locs_part = parts[0].strip()
    locs = locs_part.split(' to ')
    if len(locs) != 2:
        continue
    from_loc = locs[0].strip()
    to_loc = locs[1].strip()
    if from_loc not in travel_times:
        travel_times[from_loc] = {}
    travel_times[from_loc][to_loc] = time_val

# Define friends with their constraints
friends = [
    {'name': 'Mark', 'location': 'Marina District', 'start_avail': 18*60+45, 'end_avail': 21*60, 'min_duration': 90},
    {'name': 'Karen', 'location': 'Financial District', 'start_avail': 9*60+30, 'end_avail': 12*60+45, 'min_duration': 90},
    {'name': 'Barbara', 'location': 'Alamo Square', 'start_avail': 10*60, 'end_avail': 19*60+30, 'min_duration': 90},
    {'name': 'Nancy', 'location': 'Golden Gate Park', 'start_avail': 16*60+45, 'end_avail': 20*60, 'min_duration': 105},
    {'name': 'David', 'location': 'The Castro', 'start_avail': 9*60, 'end_avail': 18*60, 'min_duration': 120},
    {'name': 'Linda', 'location': 'Bayview', 'start_avail': 18*60+15, 'end_avail': 19*60+45, 'min_duration': 45},
    {'name': 'Kevin', 'location': 'Sunset District', 'start_avail': 10*60, 'end_avail': 17*60+45, 'min_duration': 120},
    {'name': 'Matthew', 'location': 'Haight-Ashbury', 'start_avail': 10*60+15, 'end_avail': 15*60+30, 'min_duration': 45},
    {'name': 'Andrew', 'location': 'Nob Hill', 'start_avail': 11*60+45, 'end_avail': 16*60+45, 'min_duration': 105}
]

# Initialize Z3 solver and variables
opt = Optimize()
meet_vars = {}
start_vars = {}
end_vars = {}

for friend in friends:
    name = friend['name']
    meet_var = Bool(f'meet_{name}')
    start_var = Int(f'start_{name}')
    end_var = Int(f'end_{name}')
    meet_vars[name] = meet_var
    start_vars[name] = start_var
    end_vars[name] = end_var

    # Constraints if meeting the friend
    loc = friend['location']
    start_avail = friend['start_avail']
    end_avail = friend['end_avail']
    min_dur = friend['min_duration']
    
    # Meeting time constraints
    opt.add(Implies(meet_var, start_var >= start_avail))
    opt.add(Implies(meet_var, end_var <= end_avail))
    opt.add(Implies(meet_var, end_var - start_var >= min_dur))
    
    # Travel time from Russian Hill to the friend's location
    travel_from_start = travel_times['Russian Hill'][loc]
    opt.add(Implies(meet_var, start_var >= 540 + travel_from_start))

# Pairwise constraints for meetings
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        friend_i = friends[i]
        friend_j = friends[j]
        name_i = friend_i['name']
        name_j = friend_j['name']
        meet_i = meet_vars[name_i]
        meet_j = meet_vars[name_j]
        start_i = start_vars[name_i]
        end_i = end_vars[name_i]
        start_j = start_vars[name_j]
        end_j = end_vars[name_j]
        loc_i = friend_i['location']
        loc_j = friend_j['location']
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]
        
        # Either meeting i is before j or j is before i
        opt.add(Implies(And(meet_i, meet_j),
                  Or(end_i + travel_ij <= start_j, 
                     end_j + travel_ji <= start_i)))

# Objective: maximize the number of meetings
objective = Sum([If(meet_var, 1, 0) for meet_var in meet_vars.values()])
opt.maximize(objective)

# Solve and get the model
if opt.check() == sat:
    m = opt.model()
    meetings = []
    for friend in friends:
        name = friend['name']
        meet_var = meet_vars[name]
        if m.eval(meet_var):
            start_var = start_vars[name]
            end_var = end_vars[name]
            start_val = m.eval(start_var).as_long()
            end_val = m.eval(end_var).as_long()
            start_hour = start_val // 60
            start_minute = start_val % 60
            end_hour = end_val // 60
            end_minute = end_val % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            meetings.append({
                'action': 'meet',
                'person': name,
                'start_time': start_str,
                'end_time': end_str
            })
    # Sort meetings by start time
    meetings_sorted = sorted(meetings, key=lambda x: x['start_time'])
    result = {'itinerary': meetings_sorted}
    print("SOLUTION:")
    print(json.dumps(result))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))