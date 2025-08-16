import z3
import json

# Define friends and their details
friends = [
    {
        'name': 'Anthony',
        'location': 'Haight-Ashbury',
        'availability_start': 435,  # 7:15 AM
        'availability_end': 630,    # 10:30 AM
        'required_duration': 30
    },
    {
        'name': 'Helen',
        'location': 'Pacific Heights',
        'availability_start': 480,  # 8:00 AM
        'availability_end': 720,    # 12:00 PM
        'required_duration': 75
    },
    {
        'name': 'Joshua',
        'location': 'Richmond District',
        'availability_start': 420,  # 7:00 AM
        'availability_end': 1200,   # 8:00 PM
        'required_duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Financial District',
        'availability_start': 675,  # 11:15 AM
        'availability_end': 810,    # 1:30 PM
        'required_duration': 15
    },
    {
        'name': 'William',
        'location': 'Alamo Square',
        'availability_start': 915,  # 3:15 PM
        'availability_end': 1035,   # 5:15 PM
        'required_duration': 60
    },
    {
        'name': 'Brian',
        'location': "Fisherman's Wharf",
        'availability_start': 825,  # 1:45 PM
        'availability_end': 1245,   # 8:45 PM
        'required_duration': 105
    },
    {
        'name': 'Karen',
        'location': 'Marina District',
        'availability_start': 690,  # 11:30 AM
        'availability_end': 1110,   # 6:30 PM
        'required_duration': 15
    },
    {
        'name': 'Matthew',
        'location': 'Mission District',
        'availability_start': 1035, # 5:15 PM
        'availability_end': 1155,   # 7:15 PM
        'required_duration': 120
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'availability_start': 1005, # 4:45 PM
        'availability_end': 1155,   # 7:15 PM
        'required_duration': 45
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'availability_start': 1140, # 7:00 PM
        'availability_end': 1290,   # 9:30 PM
        'required_duration': 60
    }
]

locations = [f['location'] for f in friends]

# Build travel_times dictionary
travel_data = [
    # Castro to others
    ("The Castro", "Alamo Square", 8),
    ("The Castro", "Richmond District", 16),
    ("The Castro", "Financial District", 21),
    ("The Castro", "Union Square", 19),
    ("The Castro", "Fisherman's Wharf", 24),
    ("The Castro", "Marina District", 21),
    ("The Castro", "Haight-Ashbury", 6),
    ("The Castro", "Mission District", 7),
    ("The Castro", "Pacific Heights", 16),
    ("The Castro", "Golden Gate Park", 11),
    # Alamo Square to others
    ("Alamo Square", "The Castro", 8),
    ("Alamo Square", "Richmond District", 11),
    ("Alamo Square", "Financial District", 17),
    ("Alamo Square", "Union Square", 14),
    ("Alamo Square", "Fisherman's Wharf", 19),
    ("Alamo Square", "Marina District", 15),
    ("Alamo Square", "Haight-Ashbury", 5),
    ("Alamo Square", "Mission District", 10),
    ("Alamo Square", "Pacific Heights", 10),
    ("Alamo Square", "Golden Gate Park", 9),
    # Richmond District to others
    ("Richmond District", "The Castro", 16),
    ("Richmond District", "Alamo Square", 13),
    ("Richmond District", "Financial District", 22),
    ("Richmond District", "Union Square", 21),
    ("Richmond District", "Fisherman's Wharf", 18),
    ("Richmond District", "Marina District", 9),
    ("Richmond District", "Haight-Ashbury", 10),
    ("Richmond District", "Mission District", 20),
    ("Richmond District", "Pacific Heights", 10),
    ("Richmond District", "Golden Gate Park", 9),
    # Financial District to others
    ("Financial District", "The Castro", 20),
    ("Financial District", "Alamo Square", 17),
    ("Financial District", "Richmond District", 21),
    ("Financial District", "Union Square", 9),
    ("Financial District", "Fisherman's Wharf", 10),
    ("Financial District", "Marina District", 15),
    ("Financial District", "Haight-Ashbury", 19),
    ("Financial District", "Mission District", 17),
    ("Financial District", "Pacific Heights", 13),
    ("Financial District", "Golden Gate Park", 23),
    # Union Square to others
    ("Union Square", "The Castro", 17),
    ("Union Square", "Alamo Square", 15),
    ("Union Square", "Richmond District", 20),
    ("Union Square", "Financial District", 9),
    ("Union Square", "Fisherman's Wharf", 15),
    ("Union Square", "Marina District", 18),
    ("Union Square", "Haight-Ashbury", 18),
    ("Union Square", "Mission District", 14),
    ("Union Square", "Pacific Heights", 15),
    ("Union Square", "Golden Gate Park", 22),
    # Fisherman's Wharf to others
    ("Fisherman's Wharf", "The Castro", 27),
    ("Fisherman's Wharf", "Alamo Square", 21),
    ("Fisherman's Wharf", "Richmond District", 18),
    ("Fisherman's Wharf", "Financial District", 11),
    ("Fisherman's Wharf", "Union Square", 13),
    ("Fisherman's Wharf", "Marina District", 9),
    ("Fisherman's Wharf", "Haight-Ashbury", 22),
    ("Fisherman's Wharf", "Mission District", 22),
    ("Fisherman's Wharf", "Pacific Heights", 12),
    ("Fisherman's Wharf", "Golden Gate Park", 25),
    # Marina District to others
    ("Marina District", "The Castro", 22),
    ("Marina District", "Alamo Square", 15),
    ("Marina District", "Richmond District", 11),
    ("Marina District", "Financial District", 17),
    ("Marina District", "Union Square", 16),
    ("Marina District", "Fisherman's Wharf", 10),
    ("Marina District", "Haight-Ashbury", 16),
    ("Marina District", "Mission District", 20),
    ("Marina District", "Pacific Heights", 7),
    ("Marina District", "Golden Gate Park", 18),
    # Haight-Ashbury to others
    ("Haight-Ashbury", "The Castro", 6),
    ("Haight-Ashbury", "Alamo Square", 5),
    ("Haight-Ashbury", "Richmond District", 10),
    ("Haight-Ashbury", "Financial District", 21),
    ("Haight-Ashbury", "Union Square", 19),
    ("Haight-Ashbury", "Fisherman's Wharf", 23),
    ("Haight-Ashbury", "Marina District", 17),
    ("Haight-Ashbury", "Mission District", 11),
    ("Haight-Ashbury", "Pacific Heights", 12),
    ("Haight-Ashbury", "Golden Gate Park", 7),
    # Mission District to others
    ("Mission District", "The Castro", 7),
    ("Mission District", "Alamo Square", 11),
    ("Mission District", "Richmond District", 20),
    ("Mission District", "Financial District", 15),
    ("Mission District", "Union Square", 15),
    ("Mission District", "Fisherman's Wharf", 22),
    ("Mission District", "Marina District", 19),
    ("Mission District", "Haight-Ashbury", 12),
    ("Mission District", "Pacific Heights", 16),
    ("Mission District", "Golden Gate Park", 17),
    # Pacific Heights to others
    ("Pacific Heights", "The Castro", 16),
    ("Pacific Heights", "Alamo Square", 10),
    ("Pacific Heights", "Richmond District", 12),
    ("Pacific Heights", "Financial District", 13),
    ("Pacific Heights", "Union Square", 12),
    ("Pacific Heights", "Fisherman's Wharf", 13),
    ("Pacific Heights", "Marina District", 6),
    ("Pacific Heights", "Haight-Ashbury", 11),
    ("Pacific Heights", "Mission District", 15),
    ("Pacific Heights", "Golden Gate Park", 15),
    # Golden Gate Park to others
    ("Golden Gate Park", "The Castro", 13),
    ("Golden Gate Park", "Alamo Square", 9),
    ("Golden Gate Park", "Richmond District", 7),
    ("Golden Gate Park", "Financial District", 26),
    ("Golden Gate Park", "Union Square", 22),
    ("Golden Gate Park", "Fisherman's Wharf", 24),
    ("Golden Gate Park", "Marina District", 16),
    ("Golden Gate Park", "Haight-Ashbury", 7),
    ("Golden Gate Park", "Mission District", 17),
    ("Golden Gate Park", "Pacific Heights", 16),
]

travel_times = {}
for from_loc, to_loc, time in travel_data:
    travel_times[(from_loc, to_loc)] = time

# Build travel_time_between matrix
num_friends = len(friends)
travel_time_between = [[0 for _ in range(num_friends)] for _ in range(num_friends)]

for f_prev in range(num_friends):
    for f_current in range(num_friends):
        from_loc = friends[f_prev]['location']
        to_loc = friends[f_current]['location']
        if (from_loc, to_loc) in travel_times:
            travel_time_between[f_prev][f_current] = travel_times[(from_loc, to_loc)]
        else:
            pass

# Z3 setup
opt = z3.Optimize()

num_steps = 10

# Variables
friend_vars = [z3.Int(f'friend_{i}') for i in range(num_steps)]
arrival_time_vars = [z3.Int(f'arrival_time_{i}') for i in range(num_steps)]
start_time_vars = [z3.Int(f'start_time_{i}') for i in range(num_steps)]
end_time_vars = [z3.Int(f'end_time_{i}') for i in range(num_steps)]

# Constraints for friend_vars to be between -1 and 9
for i in range(num_steps):
    opt.add(z3.And(friend_vars[i] >= -1, friend_vars[i] <= 9))

# Constraints for uniqueness of friends
for i in range(num_steps):
    for j in range(i+1, num_steps):
        opt.add(z3.Implies(z3.And(friend_vars[i] >= 0, friend_vars[j] >= 0), friend_vars[i] != friend_vars[j]))

# Constraints for arrival_time_vars
for i in range(num_steps):
    for f in range(num_friends):
        if i == 0:
            from_loc = "The Castro"
            to_loc = friends[f]['location']
            time = travel_times[(from_loc, to_loc)]
            opt.add(z3.Implies(friend_vars[i] == f, arrival_time_vars[i] == 540 + time))
        else:
            pass

for i in range(1, num_steps):
    for f_prev in range(num_friends):
        for f_current in range(num_friends):
            time = travel_time_between[f_prev][f_current]
            opt.add(z3.Implies(z3.And(friend_vars[i-1] == f_prev, friend_vars[i] == f_current), 
                               arrival_time_vars[i] == end_time_vars[i-1] + time))

# Constraints for start_time, end_time, availability
for i in range(num_steps):
    for f in range(num_friends):
        # start_time >= arrival_time
        opt.add(z3.Implies(friend_vars[i] == f, start_time_vars[i] >= arrival_time_vars[i]))
        # end_time = start_time + required_duration
        opt.add(z3.Implies(friend_vars[i] == f, end_time_vars[i] == start_time_vars[i] + friends[f]['required_duration']))
        # start_time >= availability_start
        opt.add(z3.Implies(friend_vars[i] == f, start_time_vars[i] >= friends[f]['availability_start']))
        # end_time <= availability_end
        opt.add(z3.Implies(friend_vars[i] == f, end_time_vars[i] <= friends[f]['availability_end']))

# Objective: maximize the number of friends met
count = z3.Sum([z3.If(friend_vars[i] >= 0, 1, 0) for i in range(num_steps)])
opt.maximize(count)

# Solve
if opt.check() == z3.sat:
    model = opt.model()
    # Extract the friends met
    meetings = []
    for i in range(num_steps):
        f_val = model.evaluate(friend_vars[i])
        if f_val.as_long() >= 0:
            f_index = f_val.as_long()
            start = model.evaluate(start_time_vars[i]).as_long()
            end = model.evaluate(end_time_vars[i]).as_long()
            name = friends[f_index]['name']
            meetings.append({
                'person': name,
                'start_time': f"{start // 60:02d}:{start % 60:02d}",
                'end_time': f"{end // 60:02d}:{end % 60:02d}"
            })
    # Sort meetings by start time
    meetings.sort(key=lambda x: x['start_time'])
    # Output the JSON
    print('SOLUTION:')
    print(json.dumps({"itinerary": meetings}, indent=2))
else:
    print("No solution found.")