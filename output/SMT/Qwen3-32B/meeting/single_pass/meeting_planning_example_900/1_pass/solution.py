import z3
import json

# Define all districts and travel times
districts = ['Richmond District', 'The Castro', 'Nob Hill', 'Marina District', 'Pacific Heights', 'Haight-Ashbury', 'Mission District', 'Chinatown', 'Russian Hill', 'Alamo Square', 'Bayview']

# Initialize travel times dictionary
travel_times = {d: {d2: 0 for d2 in districts} for d in districts}

# Manually input the travel times based on the given data
travel_times['Richmond District']['The Castro'] = 16
travel_times['Richmond District']['Nob Hill'] = 17
travel_times['Richmond District']['Marina District'] = 9
travel_times['Richmond District']['Pacific Heights'] = 10
travel_times['Richmond District']['Haight-Ashbury'] = 10
travel_times['Richmond District']['Mission District'] = 20
travel_times['Richmond District']['Chinatown'] = 20
travel_times['Richmond District']['Russian Hill'] = 13
travel_times['Richmond District']['Alamo Square'] = 13
travel_times['Richmond District']['Bayview'] = 27

travel_times['The Castro']['Richmond District'] = 16
travel_times['The Castro']['Nob Hill'] = 16
travel_times['The Castro']['Marina District'] = 21
travel_times['The Castro']['Pacific Heights'] = 16
travel_times['The Castro']['Haight-Ashbury'] = 6
travel_times['The Castro']['Mission District'] = 7
travel_times['The Castro']['Chinatown'] = 22
travel_times['The Castro']['Russian Hill'] = 18
travel_times['The Castro']['Alamo Square'] = 8
travel_times['The Castro']['Bayview'] = 19

travel_times['Nob Hill']['Richmond District'] = 14
travel_times['Nob Hill']['The Castro'] = 17
travel_times['Nob Hill']['Marina District'] = 11
travel_times['Nob Hill']['Pacific Heights'] = 8
travel_times['Nob Hill']['Haight-Ashbury'] = 13
travel_times['Nob Hill']['Mission District'] = 13
travel_times['Nob Hill']['Chinatown'] = 6
travel_times['Nob Hill']['Russian Hill'] = 5
travel_times['Nob Hill']['Alamo Square'] = 11
travel_times['Nob Hill']['Bayview'] = 19

travel_times['Marina District']['Richmond District'] = 11
travel_times['Marina District']['The Castro'] = 22
travel_times['Marina District']['Nob Hill'] = 12
travel_times['Marina District']['Pacific Heights'] = 7
travel_times['Marina District']['Haight-Ashbury'] = 16
travel_times['Marina District']['Mission District'] = 20
travel_times['Marina District']['Chinatown'] = 15
travel_times['Marina District']['Russian Hill'] = 8
travel_times['Marina District']['Alamo Square'] = 15
travel_times['Marina District']['Bayview'] = 27

travel_times['Pacific Heights']['Richmond District'] = 12
travel_times['Pacific Heights']['The Castro'] = 16
travel_times['Pacific Heights']['Nob Hill'] = 8
travel_times['Pacific Heights']['Marina District'] = 6
travel_times['Pacific Heights']['Haight-Ashbury'] = 11
travel_times['Pacific Heights']['Mission District'] = 15
travel_times['Pacific Heights']['Chinatown'] = 11
travel_times['Pacific Heights']['Russian Hill'] = 7
travel_times['Pacific Heights']['Alamo Square'] = 10
travel_times['Pacific Heights']['Bayview'] = 22

travel_times['Haight-Ashbury']['Richmond District'] = 10
travel_times['Haight-Ashbury']['The Castro'] = 6
travel_times['Haight-Ashbury']['Nob Hill'] = 15
travel_times['Haight-Ashbury']['Marina District'] = 17
travel_times['Haight-Ashbury']['Pacific Heights'] = 12
travel_times['Haight-Ashbury']['Mission District'] = 11
travel_times['Haight-Ashbury']['Chinatown'] = 19
travel_times['Haight-Ashbury']['Russian Hill'] = 17
travel_times['Haight-Ashbury']['Alamo Square'] = 5
travel_times['Haight-Ashbury']['Bayview'] = 18

travel_times['Mission District']['Richmond District'] = 20
travel_times['Mission District']['The Castro'] = 7
travel_times['Mission District']['Nob Hill'] = 12
travel_times['Mission District']['Marina District'] = 19
travel_times['Mission District']['Pacific Heights'] = 16
travel_times['Mission District']['Haight-Ashbury'] = 12
travel_times['Mission District']['Chinatown'] = 16
travel_times['Mission District']['Russian Hill'] = 15
travel_times['Mission District']['Alamo Square'] = 11
travel_times['Mission District']['Bayview'] = 14

travel_times['Chinatown']['Richmond District'] = 20
travel_times['Chinatown']['The Castro'] = 22
travel_times['Chinatown']['Nob Hill'] = 9
travel_times['Chinatown']['Marina District'] = 12
travel_times['Chinatown']['Pacific Heights'] = 10
travel_times['Chinatown']['Haight-Ashbury'] = 19
travel_times['Chinatown']['Mission District'] = 17
travel_times['Chinatown']['Russian Hill'] = 7
travel_times['Chinatown']['Alamo Square'] = 17
travel_times['Chinatown']['Bayview'] = 20

travel_times['Russian Hill']['Richmond District'] = 14
travel_times['Russian Hill']['The Castro'] = 21
travel_times['Russian Hill']['Nob Hill'] = 5
travel_times['Russian Hill']['Marina District'] = 7
travel_times['Russian Hill']['Pacific Heights'] = 7
travel_times['Russian Hill']['Haight-Ashbury'] = 17
travel_times['Russian Hill']['Mission District'] = 16
travel_times['Russian Hill']['Chinatown'] = 9
travel_times['Russian Hill']['Alamo Square'] = 15
travel_times['Russian Hill']['Bayview'] = 23

travel_times['Alamo Square']['Richmond District'] = 11
travel_times['Alamo Square']['The Castro'] = 8
travel_times['Alamo Square']['Nob Hill'] = 11
travel_times['Alamo Square']['Marina District'] = 15
travel_times['Alamo Square']['Pacific Heights'] = 10
travel_times['Alamo Square']['Haight-Ashbury'] = 5
travel_times['Alamo Square']['Mission District'] = 10
travel_times['Alamo Square']['Chinatown'] = 15
travel_times['Alamo Square']['Russian Hill'] = 13
travel_times['Alamo Square']['Bayview'] = 16

travel_times['Bayview']['Richmond District'] = 25
travel_times['Bayview']['The Castro'] = 19
travel_times['Bayview']['Nob Hill'] = 20
travel_times['Bayview']['Marina District'] = 27
travel_times['Bayview']['Pacific Heights'] = 23
travel_times['Bayview']['Haight-Ashbury'] = 19
travel_times['Bayview']['Mission District'] = 13
travel_times['Bayview']['Chinatown'] = 19
travel_times['Bayview']['Russian Hill'] = 23
travel_times['Bayview']['Alamo Square'] = 16

# Now, define the friends' data
friends = [
    {
        'name': 'Matthew',
        'location': 'The Castro',
        'available_start': 16 * 60 + 30,  # 990
        'available_end': 20 * 60,         # 1200
        'required_duration': 45,
    },
    {
        'name': 'Rebecca',
        'location': 'Nob Hill',
        'available_start': 15 * 60 + 15,  # 915
        'available_end': 19 * 60 + 15,    # 1155
        'required_duration': 105,
    },
    {
        'name': 'Brian',
        'location': 'Marina District',
        'available_start': 14 * 60 + 15,  # 855
        'available_end': 22 * 60,         # 1320
        'required_duration': 30,
    },
    {
        'name': 'Emily',
        'location': 'Pacific Heights',
        'available_start': 11 * 60 + 15,  # 675
        'available_end': 19 * 60 + 45,    # 1185
        'required_duration': 15,
    },
    {
        'name': 'Karen',
        'location': 'Haight-Ashbury',
        'available_start': 11 * 60 + 45,  # 705
        'available_end': 17 * 60 + 30,    # 1050
        'required_duration': 30,
    },
    {
        'name': 'Stephanie',
        'location': 'Mission District',
        'available_start': 13 * 60,       # 780
        'available_end': 15 * 60 + 45,    # 945
        'required_duration': 75,
    },
    {
        'name': 'James',
        'location': 'Chinatown',
        'available_start': 14 * 60 + 30,  # 870
        'available_end': 19 * 60,         # 1140
        'required_duration': 120,
    },
    {
        'name': 'Steven',
        'location': 'Russian Hill',
        'available_start': 14 * 60,       # 840
        'available_end': 20 * 60,         # 1200
        'required_duration': 30,
    },
    {
        'name': 'Elizabeth',
        'location': 'Alamo Square',
        'available_start': 13 * 60,       # 780
        'available_end': 17 * 60 + 15,    # 1035
        'required_duration': 120,
    },
    {
        'name': 'William',
        'location': 'Bayview',
        'available_start': 18 * 60 + 15,  # 1095
        'available_end': 20 * 60 + 15,    # 1215
        'required_duration': 90,
    },
]

# Now, create Z3 variables
solver = z3.Optimize()

meet_vars = {}
start_vars = {}
end_vars = {}

for friend in friends:
    name = friend['name']
    meet_vars[name] = z3.Bool(f'meet_{name}')
    start_vars[name] = z3.Int(f'start_{name}')
    end_vars[name] = z3.Int(f'end_{name}')

# Add constraints for each friend
for friend in friends:
    name = friend['name']
    loc = friend['location']
    available_start = friend['available_start']
    available_end = friend['available_end']
    duration = friend['required_duration']
    travel_time_from_richmond = travel_times['Richmond District'][loc]

    # If meet, then start >= available_start
    solver.add(z3.Implies(meet_vars[name], start_vars[name] >= available_start))
    # end = start + duration
    solver.add(z3.Implies(meet_vars[name], end_vars[name] == start_vars[name] + duration))
    # end <= available_end
    solver.add(z3.Implies(meet_vars[name], end_vars[name] <= available_end))
    # start >= 9:00 AM (540) + travel_time_from_richmond
    solver.add(z3.Implies(meet_vars[name], start_vars[name] >= 540 + travel_time_from_richmond))

# Add pairwise constraints between friends
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        friend1 = friends[i]
        friend2 = friends[j]
        name1 = friend1['name']
        name2 = friend2['name']
        loc1 = friend1['location']
        loc2 = friend2['location']
        duration1 = friend1['required_duration']
        duration2 = friend2['required_duration']
        travel_time_1_to_2 = travel_times[loc1][loc2]
        travel_time_2_to_1 = travel_times[loc2][loc1]

        # If both are met, then either:
        # start2 >= start1 + duration1 + travel_time_1_to_2
        # or
        # start1 >= start2 + duration2 + travel_time_2_to_1
        c = z3.Implies(
            z3.And(meet_vars[name1], meet_vars[name2]),
            z3.Or(
                start_vars[name2] >= start_vars[name1] + duration1 + travel_time_1_to_2,
                start_vars[name1] >= start_vars[name2] + duration2 + travel_time_2_to_1
            )
        )
        solver.add(c)

# Maximize the number of friends met
objective = z3.Sum([z3.If(meet_vars[name], 1, 0) for name in meet_vars])
solver.maximize(objective)

# Solve
result = solver.check()
if result == z3.sat:
    model = solver.model()
    # Extract which friends are met
    met_friends = []
    for name in meet_vars:
        if model.eval(meet_vars[name]):
            start_time = model.eval(start_vars[name]).as_long()
            end_time = model.eval(end_vars[name]).as_long()
            met_friends.append({
                'action': 'meet',
                'person': name,
                'start_time': f"{start_time // 60:02}:{start_time % 60:02}",
                'end_time': f"{end_time // 60:02}:{end_time % 60:02}"
            })
    # Sort the met friends by start time
    met_friends.sort(key=lambda x: x['start_time'])
    print('SOLUTION:')
    print(json.dumps({'itinerary': met_friends}))
else:
    print("No solution found.")