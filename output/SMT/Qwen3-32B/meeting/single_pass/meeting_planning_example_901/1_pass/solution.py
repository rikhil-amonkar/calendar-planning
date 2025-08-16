import z3
import json

# Define friends and their details
friends = [
    {
        'name': 'Emily',
        'location': 'Pacific Heights',
        'available_start': 555,  # 9:15 AM
        'available_end': 825,    # 1:45 PM
        'required_duration': 120
    },
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': 825,   # 1:45 PM
        'available_end': 1125,    # 6:45 PM
        'required_duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Golden Gate Park',
        'available_start': 1125,  # 6:45 PM
        'available_end': 1275,    # 9:15 PM
        'required_duration': 75
    },
    {
        'name': 'James',
        'location': 'Embarcadero',
        'available_start': 630,   # 10:30 AM
        'available_end': 690,     # 11:30 AM
        'required_duration': 30
    },
    {
        'name': 'Linda',
        'location': 'Haight-Ashbury',
        'available_start': 450,   # 7:30 AM
        'available_end': 1155,    # 7:15 PM
        'required_duration': 15
    },
    {
        'name': 'Paul',
        'location': 'Fisherman\'s Wharf',
        'available_start': 885,   # 2:45 PM
        'available_end': 1125,    # 6:45 PM
        'required_duration': 90
    },
    {
        'name': 'Anthony',
        'location': 'Mission District',
        'available_start': 480,   # 8:00 AM
        'available_end': 885,     # 2:45 PM
        'required_duration': 105
    },
    {
        'name': 'Nancy',
        'location': 'Alamo Square',
        'available_start': 510,   # 8:30 AM
        'available_end': 825,     # 1:45 PM
        'required_duration': 120
    },
    {
        'name': 'William',
        'location': 'Bayview',
        'available_start': 1050,  # 5:30 PM
        'available_end': 1230,    # 8:30 PM
        'required_duration': 120
    },
    {
        'name': 'Margaret',
        'location': 'Richmond District',
        'available_start': 915,   # 3:15 PM
        'available_end': 1095,    # 6:15 PM
        'required_duration': 45
    }
]

# Define travel times between locations
travel_times = {
    'Russian Hill': {
        'Pacific Heights': 7,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Haight-Ashbury': 17,
        'Fisherman\'s Wharf': 7,
        'Mission District': 16,
        'Alamo Square': 15,
        'Bayview': 23,
        'Richmond District': 14
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'North Beach': 9,
        'Golden Gate Park': 15,
        'Embarcadero': 10,
        'Haight-Ashbury': 11,
        'Fisherman\'s Wharf': 13,
        'Mission District': 15,
        'Alamo Square': 10,
        'Bayview': 22,
        'Richmond District': 12
    },
    'North Beach': {
        'Russian Hill': 4,
        'Pacific Heights': 8,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Fisherman\'s Wharf': 5,
        'Mission District': 18,
        'Alamo Square': 16,
        'Bayview': 25,
        'Richmond District': 18
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Pacific Heights': 16,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Fisherman\'s Wharf': 24,
        'Mission District': 17,
        'Alamo Square': 9,
        'Bayview': 23,
        'Richmond District': 7
    },
    'Embarcadero': {
        'Russian Hill': 8,
        'Pacific Heights': 11,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Fisherman\'s Wharf': 6,
        'Mission District': 20,
        'Alamo Square': 19,
        'Bayview': 21,
        'Richmond District': 21
    },
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Pacific Heights': 12,
        'North Beach': 19,
        'Golden Gate Park': 7,
        'Embarcadero': 20,
        'Fisherman\'s Wharf': 23,
        'Mission District': 11,
        'Alamo Square': 5,
        'Bayview': 18,
        'Richmond District': 10
    },
    'Fisherman\'s Wharf': {
        'Russian Hill': 7,
        'Pacific Heights': 12,
        'North Beach': 6,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Alamo Square': 21,
        'Bayview': 26,
        'Richmond District': 18
    },
    'Mission District': {
        'Russian Hill': 15,
        'Pacific Heights': 16,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 12,
        'Fisherman\'s Wharf': 22,
        'Alamo Square': 11,
        'Bayview': 14,
        'Richmond District': 20
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Pacific Heights': 10,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Fisherman\'s Wharf': 19,
        'Mission District': 10,
        'Bayview': 16,
        'Richmond District': 13
    },
    'Bayview': {
        'Russian Hill': 23,
        'Pacific Heights': 23,
        'North Beach': 22,
        'Golden Gate Park': 22,
        'Embarcadero': 19,
        'Haight-Ashbury': 19,
        'Fisherman\'s Wharf': 25,
        'Mission District': 13,
        'Alamo Square': 16,
        'Richmond District': 25
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Pacific Heights': 10,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Fisherman\'s Wharf': 18,
        'Mission District': 20,
        'Alamo Square': 13,
        'Bayview': 27
    }
}

# Initial time at Russian Hill: 9:00 AM = 540 minutes
initial_time = 540

# Create Z3 variables
met_vars = []
arrival_vars = []
departure_vars = []

for friend in friends:
    name = friend['name']
    met = z3.Bool(f'met_{name}')
    arrival = z3.Int(f'arrival_{name}')
    departure = z3.Int(f'departure_{name}')
    met_vars.append(met)
    arrival_vars.append(arrival)
    departure_vars.append(departure)

# Create the solver
opt = z3.Optimize()

# Add constraints for each friend
for i in range(len(friends)):
    friend = friends[i]
    name = friend['name']
    location = friend['location']
    available_start = friend['available_start']
    available_end = friend['available_end']
    required_duration = friend['required_duration']
    travel_time_from_RH = travel_times['Russian Hill'][location]
    
    met = met_vars[i]
    arrival = arrival_vars[i]
    departure = departure_vars[i]
    
    # Constraints for this friend
    opt.add(z3.Implies(met, arrival >= available_start))
    opt.add(z3.Implies(met, departure == arrival + required_duration))
    opt.add(z3.Implies(met, departure <= available_end))
    opt.add(z3.Implies(met, arrival >= initial_time + travel_time_from_RH))

# Add pairwise constraints between friends
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        friend_i = friends[i]
        friend_j = friends[j]
        name_i = friend_i['name']
        name_j = friend_j['name']
        location_i = friend_i['location']
        location_j = friend_j['location']
        travel_time_i_to_j = travel_times[location_i][location_j]
        travel_time_j_to_i = travel_times[location_j][location_i]
        
        met_i = met_vars[i]
        met_j = met_vars[j]
        arrival_i = arrival_vars[i]
        departure_i = departure_vars[i]
        arrival_j = arrival_vars[j]
        departure_j = departure_vars[j]
        
        # Add constraint: if both are met, then either arrival_i >= departure_j + travel_time_j_to_i or arrival_j >= departure_i + travel_time_i_to_j
        opt.add(z3.Implies(z3.And(met_i, met_j), z3.Or(
            arrival_i >= departure_j + travel_time_j_to_i,
            arrival_j >= departure_i + travel_time_i_to_j
        )))

# Maximize the number of friends met
opt.maximize(z3.Sum([z3.If(met, 1, 0) for met in met_vars]))

# Check if the problem is satisfiable
if opt.check() == z3.sat:
    model = opt.model()
    # Collect the friends that are met
    met_friends = []
    for i in range(len(friends)):
        if model.eval(met_vars[i]):
            friend = friends[i]
            arrival_time = model.eval(arrival_vars[i]).as_long()
            departure_time = model.eval(departure_vars[i]).as_long()
            # Convert to HH:MM format
            start_time = f"{arrival_time // 60:02d}:{arrival_time % 60:02d}"
            end_time = f"{departure_time // 60:02d}:{departure_time % 60:02d}"
            met_friends.append({
                'action': 'meet',
                'person': friend['name'],
                'start_time': start_time,
                'end_time': end_time
            })
    # Sort the met friends by arrival time to determine the order
    met_friends.sort(key=lambda x: int(x['start_time'].replace(':', '')))
    # Output the JSON
    print("SOLUTION:")
    print(json.dumps({"itinerary": met_friends}, indent=2))
else:
    print("No solution found.")