from z3 import *

# Define friends
friends = [
    {
        'name': 'William',
        'location': 'Embarcadero',
        'available_start': 420,  # 7:00 AM
        'available_end': 540,    # 9:00 AM
        'required_duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'Nob Hill',
        'available_start': 450,  # 7:30 AM
        'available_end': 570,    # 9:30 AM
        'required_duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Alamo Square',
        'available_start': 690,  # 11:30 AM
        'available_end': 765,    # 12:45 PM
        'required_duration': 15
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': 930,  # 15:30 (3:30 PM)
        'available_end': 1185,   # 19:45 (7:45 PM)
        'required_duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'available_start': 945,  # 15:45 (3:45 PM)
        'available_end': 1155,   # 19:15 (7:15 PM)
        'required_duration': 30
    },
    {
        'name': 'Laura',
        'location': 'The Castro',
        'available_start': 1185, # 19:45 (7:45 PM)
        'available_end': 1290,   # 21:30 (9:30 PM)
        'required_duration': 105
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'available_start': 1275, # 21:15 (9:15 PM)
        'available_end': 1305,   # 21:45 (9:45 PM)
        'required_duration': 15
    }
]

# Define travel times
travel_times = {
    'Fisherman\'s Wharf': {
        'The Castro': 26,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Russian Hill': 7,
        'Nob Hill': 11,
        'Alamo Square': 20,
        'North Beach': 6
    },
    'The Castro': {
        'Fisherman\'s Wharf': 24,
        'Golden Gate Park': 11,
        'Embarcadero': 22,
        'Russian Hill': 18,
        'Nob Hill': 16,
        'Alamo Square': 8,
        'North Beach': 20
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'The Castro': 13,
        'Embarcadero': 25,
        'Russian Hill': 19,
        'Nob Hill': 20,
        'Alamo Square': 10,
        'North Beach': 24
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'The Castro': 25,
        'Golden Gate Park': 25,
        'Russian Hill': 8,
        'Nob Hill': 10,
        'Alamo Square': 19,
        'North Beach': 5
    },
    'Russian Hill': {
        'Fisherman\'s Wharf': 7,
        'The Castro': 21,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Nob Hill': 5,
        'Alamo Square': 15,
        'North Beach': 5
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'The Castro': 17,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Russian Hill': 5,
        'Alamo Square': 11,
        'North Beach': 8
    },
    'Alamo Square': {
        'Fisherman\'s Wharf': 19,
        'The Castro': 8,
        'Golden Gate Park': 9,
        'Embarcadero': 17,
        'Russian Hill': 13,
        'Nob Hill': 11,
        'North Beach': 15
    },
    'North Beach': {
        'Fisherman\'s Wharf': 5,
        'The Castro': 22,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Russian Hill': 4,
        'Nob Hill': 7,
        'Alamo Square': 16
    }
}

# Create solver
s = Optimize()

# Create variables
met = [Bool(f'met_{i}') for i in range(7)]
start_time = [Int(f'start_{i}') for i in range(7)]
end_time = [Int(f'end_{i}') for i in range(7)]
position = [Int(f'pos_{i}') for i in range(7)]

# Add constraints for each friend's meeting
for i in range(7):
    s.add(Implies(met[i], start_time[i] >= friends[i]['available_start']))
    s.add(Implies(met[i], end_time[i] == start_time[i] + friends[i]['required_duration']))
    s.add(Implies(met[i], end_time[i] <= friends[i]['available_end']))

# Add constraints for the first meeting
for i in range(7):
    loc_i = friends[i]['location']
    fw_to_i = travel_times['Fisherman\'s Wharf'][loc_i]
    big_and = True
    for j in range(7):
        if j != i:
            big_and = And(big_and, Implies(met[j], position[j] >= position[i]))
    s.add(Implies(And(big_and, met[i]), start_time[i] >= 540 + fw_to_i))

# Add constraints for transitions between meetings
for i in range(7):
    for j in range(7):
        if i != j:
            loc_i = friends[i]['location']
            loc_j = friends[j]['location']
            travel_time = travel_times[loc_i][loc_j]
            s.add(Implies(And(met[i], met[j], position[i] < position[j]), end_time[i] + travel_time <= start_time[j]))

# Add constraints for unique positions
for i in range(7):
    for j in range(i+1, 7):
        s.add(Implies(And(met[i], met[j]), position[i] != position[j]))

# Add objective to maximize the number of friends met
s.maximize(Sum([If(met[i], 1, 0) for i in range(7)]))

# Check for solution
if s.check() == sat:
    model = s.model()
    # Extract the met friends and their times
    met_friends = []
    for i in range(7):
        if is_true(model.evaluate(met[i])):
            st = model.evaluate(start_time[i]).as_long()
            et = model.evaluate(end_time[i]).as_long()
            pos = model.evaluate(position[i]).as_long()
            met_friends.append( (i, st, et, pos) )
    # Sort by position
    met_friends.sort(key=lambda x: x[3])
    # Convert to the required format
    itinerary = []
    for i, st, et, pos in met_friends:
        person = friends[i]['name']
        start_time_str = f"{st//60:02d}:{st%60:02d}"
        end_time_str = f"{et//60:02d}:{et%60:02d}"
        itinerary.append( {"action": "meet", "person": person, "start_time": start_time_str, "end_time": end_time_str} )
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")