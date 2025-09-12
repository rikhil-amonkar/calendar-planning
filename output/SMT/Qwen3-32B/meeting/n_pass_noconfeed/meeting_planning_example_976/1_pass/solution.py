import z3
import json

# Define the travel times between locations
travel_time = {
    'Embarcadero': {
        'Bayview': 21,
        'Chinatown': 7,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        "Fisherman's Wharf": 6,
        'Marina District': 12,
    },
    'Bayview': {
        'Embarcadero': 19,
        'Chinatown': 19,
        'Alamo Square': 16,
        'Nob Hill': 20,
        'Presidio': 32,
        'Union Square': 18,
        'The Castro': 19,
        'North Beach': 22,
        "Fisherman's Wharf": 25,
        'Marina District': 27,
    },
    'Chinatown': {
        'Embarcadero': 5,
        'Bayview': 20,
        'Alamo Square': 17,
        'Nob Hill': 9,
        'Presidio': 19,
        'Union Square': 7,
        'The Castro': 22,
        'North Beach': 3,
        "Fisherman's Wharf": 8,
        'Marina District': 12,
    },
    'Alamo Square': {
        'Embarcadero': 16,
        'Bayview': 16,
        'Chinatown': 15,
        'Nob Hill': 11,
        'Presidio': 17,
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        "Fisherman's Wharf": 19,
        'Marina District': 15,
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Bayview': 19,
        'Chinatown': 6,
        'Alamo Square': 11,
        'Presidio': 17,
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        "Fisherman's Wharf": 10,
        'Marina District': 11,
    },
    'Presidio': {
        'Embarcadero': 20,
        'Bayview': 31,
        'Chinatown': 21,
        'Alamo Square': 19,
        'Nob Hill': 18,
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        "Fisherman's Wharf": 19,
        'Marina District': 11,
    },
    'Union Square': {
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        'The Castro': 17,
        'North Beach': 10,
        "Fisherman's Wharf": 15,
        'Marina District': 18,
    },
    'The Castro': {
        'Embarcadero': 22,
        'Bayview': 19,
        'Chinatown': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        'Union Square': 19,
        'North Beach': 20,
        "Fisherman's Wharf": 24,
        'Marina District': 21,
    },
    'North Beach': {
        'Embarcadero': 6,
        'Bayview': 25,
        'Chinatown': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        'Union Square': 7,
        'The Castro': 23,
        "Fisherman's Wharf": 5,
        'Marina District': 9,
    },
    "Fisherman's Wharf": {
        'Embarcadero': 8,
        'Bayview': 26,
        'Chinatown': 12,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Marina District': 9,
    },
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Chinatown': 15,
        'Alamo Square': 15,
        'Nob Hill': 12,
        'Presidio': 10,
        'Union Square': 16,
        'The Castro': 22,
        'North Beach': 11,
        "Fisherman's Wharf": 10,
    }
}

# Define friends' data
friends_data = [
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': 7 * 60 + 30,  # 7:30 AM
        'available_end': 10 * 60 + 15,   # 10:15 AM
        'min_duration': 60,
    },
    {
        'name': 'Brian',
        'location': 'Marina District',
        'available_start': 12 * 60 + 15,  # 12:15 PM
        'available_end': 18 * 60,         # 6:00 PM
        'min_duration': 60,
    },
    {
        'name': 'Nancy',
        'location': 'North Beach',
        'available_start': 14 * 60 + 45,  # 2:45 PM
        'available_end': 20 * 60,         # 8:00 PM
        'min_duration': 15,
    },
    {
        'name': 'Thomas',
        'location': "Fisherman's Wharf",
        'available_start': 13 * 60 + 30,  # 1:30 PM
        'available_end': 19 * 60,         # 7:00 PM
        'min_duration': 30,
    },
    {
        'name': 'Jessica',
        'location': 'Nob Hill',
        'available_start': 16 * 60 + 30,  # 4:30 PM
        'available_end': 18 * 60 + 45,    # 6:45 PM
        'min_duration': 120,
    },
    {
        'name': 'Mary',
        'location': 'Union Square',
        'available_start': 16 * 60 + 45,  # 4:45 PM
        'available_end': 21 * 60 + 30,    # 9:30 PM
        'min_duration': 60,
    },
    {
        'name': 'Charles',
        'location': 'The Castro',
        'available_start': 16 * 60 + 30,  # 4:30 PM
        'available_end': 22 * 60,         # 10:00 PM
        'min_duration': 105,
    },
    {
        'name': 'Matthew',
        'location': 'Bayview',
        'available_start': 19 * 60 + 15,  # 7:15 PM
        'available_end': 22 * 60,         # 10:00 PM
        'min_duration': 120,
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'available_start': 19 * 60 + 15,  # 7:15 PM
        'available_end': 21 * 60 + 15,    # 9:15 PM
        'min_duration': 90,
    },
    {
        'name': 'Sarah',
        'location': 'Alamo Square',
        'available_start': 20 * 60,       # 8:00 PM
        'available_end': 21 * 60 + 45,    # 9:45 PM
        'min_duration': 105,
    },
]

# Create Z3 variables for each friend
solver = z3.Optimize()

meet_vars = {}
start_vars = {}
end_vars = {}

for friend in friends_data:
    name = friend['name']
    meet = z3.Bool(f'meet_{name}')
    start = z3.Int(f'start_{name}')
    end = z3.Int(f'end_{name}')
    meet_vars[name] = meet
    start_vars[name] = start
    end_vars[name] = end
    solver.add(z3.Implies(meet, start >= 540 + travel_time['Embarcadero'][friend['location']]))  # arrival time is 540 (9:00 AM)
    solver.add(z3.Implies(meet, start >= friend['available_start']))
    solver.add(z3.Implies(meet, end <= friend['available_end']))
    solver.add(z3.Implies(meet, end - start >= friend['min_duration']))

# Add pairwise constraints between all friends
for i in range(len(friends_data)):
    for j in range(i + 1, len(friends_data)):
        friend1 = friends_data[i]
        friend2 = friends_data[j]
        name1 = friend1['name']
        name2 = friend2['name']
        loc1 = friend1['location']
        loc2 = friend2['location']
        meet1 = meet_vars[name1]
        meet2 = meet_vars[name2]
        start1 = start_vars[name1]
        end1 = end_vars[name1]
        start2 = start_vars[name2]
        end2 = end_vars[name2]
        travel1to2 = travel_time[loc1][loc2]
        travel2to1 = travel_time[loc2][loc1]
        # If both friends are met, then the meetings are ordered with travel time considered
        solver.add(z3.Implies(z3.And(meet1, meet2),
                              z3.Or(
                                  start2 >= end1 + travel1to2,
                                  start1 >= end2 + travel2to1
                              )))

# Maximize the number of friends met
num_meet = sum(meet_vars.values())
solver.maximize(num_meet)

# Check if the problem is satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    result = []
    for friend in friends_data:
        name = friend['name']
        meet = model.eval(meet_vars[name])
        if meet:
            start_time = model.eval(start_vars[name]).as_long()
            end_time = model.eval(end_vars[name]).as_long()
            # Convert start and end times to H:MM format
            start_h = start_time // 60
            start_m = start_time % 60
            end_h = end_time // 60
            end_m = end_time % 60
            result.append({
                "action": "meet",
                "location": friend['location'],
                "person": name,
                "start_time": f"{start_h}:{start_m:02d}",
                "end_time": f"{end_h}:{end_m:02d}"
            })
    # Sort the result by start time
    result.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": result}, indent=2))
else:
    print("No solution found.")