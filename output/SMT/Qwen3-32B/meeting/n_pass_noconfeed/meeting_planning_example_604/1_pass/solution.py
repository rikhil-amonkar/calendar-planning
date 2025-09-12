import z3
import json

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define friends
friends = [
    {
        'name': 'Laura',
        'location': 'The Castro',  # index 1
        'available_start': 1185,    # 7:45 PM
        'available_end': 1290,      # 9:30 PM
        'required': 105
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',  # index 2
        'available_start': 1275,          # 9:15 PM
        'available_end': 1305,            # 9:45 PM
        'required': 15
    },
    {
        'name': 'William',
        'location': 'Embarcadero',  # index 3
        'available_start': 420,      # 7:00 AM
        'available_end': 540,        # 9:00 AM
        'required': 90
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',  # index 4
        'available_start': 870,       # 2:30 PM
        'available_end': 1185,        # 7:45 PM
        'required': 30
    },
    {
        'name': 'Stephanie',
        'location': 'Nob Hill',  # index 5
        'available_start': 450,   # 7:30 AM
        'available_end': 570,     # 9:30 AM
        'required': 45
    },
    {
        'name': 'Joseph',
        'location': 'Alamo Square',  # index 6
        'available_start': 690,       # 11:30 AM
        'available_end': 765,         # 12:45 PM
        'required': 15
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',  # index 7
        'available_start': 945,      # 3:45 PM
        'available_end': 1155,       # 7:15 PM
        'required': 30
    }
]

# Location indexes for each friend
loc = [1, 2, 3, 4, 5, 6, 7]  # friends[0] is Laura at index 1, etc.

# Travel times between locations (as per problem input)
travel_times = [
    # Fisherman's Wharf to all
    [0, 26, 25, 8, 7, 11, 20, 6],
    # The Castro to all
    [24, 0, 11, 22, 18, 16, 8, 20],
    # Golden Gate Park to all
    [24, 13, 0, 25, 19, 20, 10, 24],
    # Embarcadero to all
    [6, 25, 25, 0, 8, 10, 19, 5],
    # Russian Hill to all
    [7, 21, 21, 8, 0, 5, 15, 5],
    # Nob Hill to all
    [11, 17, 17, 9, 5, 0, 11, 8],
    # Alamo Square to all
    [19, 8, 9, 17, 13, 11, 0, 15],
    # North Beach to all
    [5, 22, 22, 6, 4, 7, 16, 0]
]

arrival_time = 540  # 9:00 AM in minutes

solver = z3.Optimize()

include = [solver.Bool(f'include_{i}') for i in range(7)]
start = [solver.Int(f'start_{i}') for i in range(7)]
end = [solver.Int(f'end_{i}') for i in range(7)]
pos = [solver.Int(f'pos_{i}') for i in range(7)]

for i in range(7):
    # If included, start and end times must be within available window
    solver.add(z3.Implies(include[i], start[i] >= friends[i]['available_start']))
    solver.add(z3.Implies(include[i], end[i] <= friends[i]['available_end']))
    # Duration requirement
    solver.add(z3.Implies(include[i], end[i] - start[i] >= friends[i]['required']))

    # First in sequence: start time >= arrival_time + travel_time from Fisherman's Wharf to location
    travel_time_from_start = travel_times[0][loc[i]]
    solver.add(z3.Implies(z3.And(include[i], pos[i] == 0), start[i] >= arrival_time + travel_time_from_start))

# Constraints for pairs of friends
for i in range(7):
    for j in range(7):
        if i != j:
            # If both included and pos[i] < pos[j], then start[j] >= end[i] + travel time from i's loc to j's loc
            loc_i = loc[i]
            loc_j = loc[j]
            travel_time = travel_times[loc_i][loc_j]
            cond = z3.And(include[i], include[j], pos[i] < pos[j])
            impl = z3.Implies(cond, start[j] >= end[i] + travel_time)
            solver.add(impl)

# Ensure positions are unique for included friends
for i in range(7):
    for j in range(i+1, 7):
        cond = z3.And(include[i], include[j])
        impl = z3.Implies(cond, pos[i] != pos[j])
        solver.add(impl)

# Maximize the number of included friends
solver.maximize(z3.Sum([z3.If(include[i], 1, 0) for i in range(7)]))

if solver.check() == z3.sat:
    model = solver.model()
    # Collect included friends
    included = []
    for i in range(7):
        if model.evaluate(include[i]):
            included.append({
                'index': i,
                'start': model.evaluate(start[i]).as_long(),
                'end': model.evaluate(end[i]).as_long(),
                'pos': model.evaluate(pos[i]).as_long()
            })
    # Sort by position
    included.sort(key=lambda x: x['pos'])
    # Generate itinerary
    itinerary = []
    for item in included:
        i = item['index']
        friend = friends[i]
        start_time = to_time_str(item['start'])
        end_time = to_time_str(item['end'])
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_time,
            "end_time": end_time
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")