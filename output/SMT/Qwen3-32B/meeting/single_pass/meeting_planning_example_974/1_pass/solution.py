import z3
import json

# Define the friends and their data
friends = [
    {
        'name': 'Charles',
        'location': 'Presidio',
        'available_start': 795,  # 13:15
        'available_end': 900,    # 15:00
        'required_duration': 105,
    },
    {
        'name': 'Robert',
        'location': 'Nob Hill',
        'available_start': 795,
        'available_end': 1050,
        'required_duration': 90,
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'available_start': 885,
        'available_end': 1320,
        'required_duration': 105,
    },
    {
        'name': 'Brian',
        'location': 'Mission District',
        'available_start': 930,
        'available_end': 1320,
        'required_duration': 60,
    },
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'available_start': 1020,
        'available_end': 1185,
        'required_duration': 75,
    },
    {
        'name': 'David',
        'location': 'North Beach',
        'available_start': 885,
        'available_end': 990,
        'required_duration': 75,
    },
    {
        'name': 'William',
        'location': 'Russian Hill',
        'available_start': 750,
        'available_end': 1155,
        'required_duration': 120,
    },
    {
        'name': 'Jeffrey',
        'location': 'Richmond District',
        'available_start': 720,
        'available_end': 1155,
        'required_duration': 45,
    },
    {
        'name': 'Karen',
        'location': 'Embarcadero',
        'available_start': 855,
        'available_end': 1245,
        'required_duration': 60,
    },
    {
        'name': 'Joshua',
        'location': 'Alamo Square',
        'available_start': 1125,
        'available_end': 1320,
        'required_duration': 60,
    },
]

# Define travel times between districts
travel_times = {
    'Sunset District': {
        'Presidio': 16,
        'Nob Hill': 27,
        'Pacific Heights': 21,
        'Mission District': 25,
        'Marina District': 21,
        'North Beach': 28,
        'Russian Hill': 24,
        'Richmond District': 12,
        'Embarcadero': 30,
        'Alamo Square': 17,
    },
    'Presidio': {
        'Sunset District': 15,
        'Nob Hill': 18,
        'Pacific Heights': 11,
        'Mission District': 26,
        'Marina District': 11,
        'North Beach': 18,
        'Russian Hill': 14,
        'Richmond District': 7,
        'Embarcadero': 20,
        'Alamo Square': 19,
    },
    'Nob Hill': {
        'Sunset District': 24,
        'Presidio': 17,
        'Pacific Heights': 8,
        'Mission District': 13,
        'Marina District': 11,
        'North Beach': 8,
        'Russian Hill': 5,
        'Richmond District': 14,
        'Embarcadero': 9,
        'Alamo Square': 11,
    },
    'Pacific Heights': {
        'Sunset District': 21,
        'Presidio': 11,
        'Nob Hill': 8,
        'Mission District': 15,
        'Marina District': 6,
        'North Beach': 9,
        'Russian Hill': 7,
        'Richmond District': 12,
        'Embarcadero': 10,
        'Alamo Square': 10,
    },
    'Mission District': {
        'Sunset District': 24,
        'Presidio': 25,
        'Nob Hill': 12,
        'Pacific Heights': 16,
        'Marina District': 19,
        'North Beach': 17,
        'Russian Hill': 15,
        'Richmond District': 20,
        'Embarcadero': 19,
        'Alamo Square': 11,
    },
    'Marina District': {
        'Sunset District': 19,
        'Presidio': 10,
        'Nob Hill': 12,
        'Pacific Heights': 7,
        'Mission District': 20,
        'North Beach': 11,
        'Russian Hill': 8,
        'Richmond District': 11,
        'Embarcadero': 14,
        'Alamo Square': 15,
    },
    'North Beach': {
        'Sunset District': 27,
        'Presidio': 17,
        'Nob Hill': 7,
        'Pacific Heights': 8,
        'Mission District': 18,
        'Marina District': 9,
        'Russian Hill': 4,
        'Richmond District': 18,
        'Embarcadero': 6,
        'Alamo Square': 16,
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Presidio': 14,
        'Nob Hill': 5,
        'Pacific Heights': 7,
        'Mission District': 16,
        'Marina District': 7,
        'North Beach': 5,
        'Richmond District': 14,
        'Embarcadero': 8,
        'Alamo Square': 15,
    },
    'Richmond District': {
        'Sunset District': 11,
        'Presidio': 7,
        'Nob Hill': 17,
        'Pacific Heights': 10,
        'Mission District': 20,
        'Marina District': 9,
        'North Beach': 17,
        'Russian Hill': 13,
        'Embarcadero': 19,
        'Alamo Square': 13,
    },
    'Embarcadero': {
        'Sunset District': 30,
        'Presidio': 20,
        'Nob Hill': 10,
        'Pacific Heights': 11,
        'Mission District': 20,
        'Marina District': 12,
        'North Beach': 5,
        'Russian Hill': 8,
        'Richmond District': 21,
        'Alamo Square': 19,
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Presidio': 17,
        'Nob Hill': 11,
        'Pacific Heights': 10,
        'Mission District': 10,
        'Marina District': 15,
        'North Beach': 15,
        'Russian Hill': 13,
        'Richmond District': 11,
        'Embarcadero': 16,
    },
}

# Z3 solver setup
solver = z3.Solver()

num_friends = len(friends)
include = [z3.Bool(f'include_{i}') for i in range(num_friends)]
start = [z3.Int(f'start_{i}') for i in range(num_friends)]
end = [z3.Int(f'end_{i}') for i in range(num_friends)]

# Initial time (9:00 AM = 540 minutes)
initial_time = 540

# Add constraints for each friend
for i in range(num_friends):
    friend = friends[i]
    loc = friend['location']
    # If included, start >= available_start
    solver.add(z3.Implies(include[i], start[i] >= friend['available_start']))
    # If included, end <= available_end
    solver.add(z3.Implies(include[i], end[i] <= friend['available_end']))
    # If included, end - start >= required_duration
    solver.add(z3.Implies(include[i], end[i] - start[i] >= friend['required_duration']))
    # If included, start >= initial_time + travel_time from Sunset to location
    travel_time = travel_times['Sunset District'][loc]
    solver.add(z3.Implies(include[i], start[i] >= initial_time + travel_time))

# Add constraints for all pairs of friends
for i in range(num_friends):
    for j in range(i + 1, num_friends):
        friend_i = friends[i]
        friend_j = friends[j]
        loc_i = friend_i['location']
        loc_j = friend_j['location']
        travel_time_ij = travel_times[loc_i][loc_j]
        travel_time_ji = travel_times[loc_j][loc_i]

        # If both are included, then if start_i < start_j, end_i + travel_time_ij <= start_j
        cond1 = z3.And(include[i], include[j], start[i] < start[j])
        constraint1 = z3.Implies(cond1, end[i] + travel_time_ij <= start[j])
        solver.add(constraint1)

        # If both are included, then if start_j < start_i, end_j + travel_time_ji <= start_i
        cond2 = z3.And(include[i], include[j], start[j] < start[i])
        constraint2 = z3.Implies(cond2, end[j] + travel_time_ji <= start[i])
        solver.add(constraint2)

# Maximize the number of friends included
num_included = z3.Sum([z3.If(include[i], 1, 0) for i in range(num_friends)])
solver.maximize(num_included)

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(num_friends):
        if model.evaluate(include[i]):
            friend = friends[i]
            start_time = model.evaluate(start[i])
            end_time = model.evaluate(end[i])
            # Convert to HH:MM format
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours:02d}:{mins:02d}"
            start_str = to_time_str(start_time)
            end_str = to_time_str(end_time)
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_str,
                "end_time": end_str,
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")