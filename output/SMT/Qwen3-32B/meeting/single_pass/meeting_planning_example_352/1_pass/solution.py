import json
from z3 import *

# Define friends and their data
friends = [
    {'name': 'Sandra', 'location': 'Chinatown', 'available_start': 435, 'available_end': 1155, 'duration': 75},
    {'name': 'Nancy', 'location': 'Marina District', 'available_start': 660, 'available_end': 1215, 'duration': 105},
    {'name': 'Joseph', 'location': 'Haight-Ashbury', 'available_start': 750, 'available_end': 1185, 'duration': 90},
    {'name': 'Karen', 'location': 'Nob Hill', 'available_start': 1275, 'available_end': 1305, 'duration': 30},
]

# Define locations for each friend
locations = ['Chinatown', 'Marina District', 'Haight-Ashbury', 'Nob Hill']

# Travel times between locations
travel_times = {
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Marina District'): 18,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Marina District'): 11,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Nob Hill'): 8,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Chinatown'): 16,
}

# Create travel time matrix between friends
travel_time_matrix = [[0]*4 for _ in range(4)]
for i in range(4):
    from_loc = locations[i]
    for j in range(4):
        to_loc = locations[j]
        travel_time_matrix[i][j] = travel_times[(from_loc, to_loc)]

# Initial travel times from Union Square to each friend's location
initial_travel_times = [7, 18, 18, 9]  # Chinatown, Marina District, Haight-Ashbury, Nob Hill

# Z3 solver setup
s = Solver()

# Define variables
order = [Int(f'order_{i}') for i in range(4)]
arrival_time = [Int(f'arrival_{i}') for i in range(4)]
start_time = [Int(f'start_{i}') for i in range(4)]
end_time = [Int(f'end_{i}') for i in range(4)]

# Constraints for order variables
for i in range(4):
    s.add(And(order[i] >= 0, order[i] <= 3))
s.add(Distinct(order))

# Arrival time for position 0
s.add(arrival_time[0] == 540 + If(order[0] == 0, 7,
                                 If(order[0] == 1, 18,
                                 If(order[0] == 2, 18,
                                 If(order[0] == 3, 9, 0)))))

# Arrival time for position 1
travel_time_1 = 0
for k in range(4):
    for m in range(4):
        if k == m:
            continue
        cond = And(order[0] == k, order[1] == m)
        travel_time_1 += If(cond, travel_time_matrix[k][m], 0)
s.add(arrival_time[1] == end_time[0] + travel_time_1)

# Arrival time for position 2
travel_time_2 = 0
for k in range(4):
    for m in range(4):
        if k == m:
            continue
        cond = And(order[1] == k, order[2] == m)
        travel_time_2 += If(cond, travel_time_matrix[k][m], 0)
s.add(arrival_time[2] == end_time[1] + travel_time_2)

# Arrival time for position 3
travel_time_3 = 0
for k in range(4):
    for m in range(4):
        if k == m:
            continue
        cond = And(order[2] == k, order[3] == m)
        travel_time_3 += If(cond, travel_time_matrix[k][m], 0)
s.add(arrival_time[3] == end_time[2] + travel_time_3)

# Add constraints for start and end times based on friend's data
for i in range(4):
    for friend_index in range(4):
        if friend_index == 3:  # Karen
            s.add(Implies(order[i] == friend_index, start_time[i] == 1275))
            s.add(Implies(order[i] == friend_index, end_time[i] == 1305))
        else:
            f = friends[friend_index]
            s.add(Implies(order[i] == friend_index, start_time[i] >= arrival_time[i]))
            s.add(Implies(order[i] == friend_index, start_time[i] >= f['available_start']))
            s.add(Implies(order[i] == friend_index, start_time[i] + f['duration'] <= f['available_end']))
            s.add(Implies(order[i] == friend_index, end_time[i] == start_time[i] + f['duration']))

# Check for solution
if s.check() == sat:
    model = s.model()
    order_values = [model.evaluate(order[i]).as_long() for i in range(4)]
    start_values = [model.evaluate(start_time[i]).as_long() for i in range(4)]
    end_values = [model.evaluate(end_time[i]).as_long() for i in range(4)]
    
    def to_time_str(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    itinerary = []
    for i in range(4):
        friend_index = order_values[i]
        friend_name = friends[friend_index]['name']
        start = start_values[i]
        end = end_values[i]
        start_str = to_time_str(start)
        end_str = to_time_str(end)
        itinerary.append({"action": "meet", "person": friend_name, "start_time": start_str, "end_time": end_str})
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")