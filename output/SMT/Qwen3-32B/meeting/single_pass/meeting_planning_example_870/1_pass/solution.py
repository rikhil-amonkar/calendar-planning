from z3 import *

# Define friends and travel_time
friends = [
    {'index':0, 'name':'Carol', 'location':5, 'available_start':615, 'available_end':720, 'duration':60},
    {'index':1, 'name':'Sandra', 'location':8, 'available_start':555, 'available_end':1170, 'duration':60},
    {'index':2, 'name':'Brian', 'location':6, 'available_start':600, 'available_end':1290, 'duration':75},
    {'index':3, 'name':'Kenneth', 'location':2, 'available_start':885, 'available_end':975, 'duration':30},
    {'index':4, 'name':'Kimberly', 'location':3, 'available_start':855, 'available_end':1320, 'duration':30},
    {'index':5, 'name':'Laura', 'location':7, 'available_start':975, 'available_end':1230, 'duration':30},
    {'index':6, 'name':'Linda', 'location':1, 'available_start':1080, 'available_end':1320, 'duration':30},
    {'index':7, 'name':'Karen', 'location':9, 'available_start':1170, 'available_end':1320, 'duration':75},
    {'index':8, 'name':'Paul', 'location':4, 'available_start':1260, 'available_end':1290, 'duration':15},
]

travel_time = [
    [0, 6, 16, 12, 10, 13, 11, 15, 8, 7],
    [6, 0, 22, 11, 15, 17, 10, 20, 12, 8],
    [16, 21, 0, 16, 8, 21, 20, 7, 16, 18],
    [10, 9, 16, 0, 13, 22, 7, 20, 17, 13],
    [10, 15, 8, 11, 0, 17, 17, 10, 11, 13],
    [13, 15, 20, 21, 17, 0, 22, 17, 9, 11],
    [11, 11, 21, 7, 19, 23, 0, 26, 18, 14],
    [16, 19, 7, 20, 11, 15, 25, 0, 12, 15],
    [8, 11, 17, 14, 11, 9, 17, 13, 0, 5],
    [7, 7, 21, 14, 15, 11, 14, 16, 5, 0],
]

friend_locations = [f['location'] for f in friends]
friend_available_start = [f['available_start'] for f in friends]
friend_available_end = [f['available_end'] for f in friends]
friend_durations = [f['duration'] for f in friends]

positions = 9  # maximum number of friends to visit
solver = Optimize()

# Create variables
friend_vars = [Int('friend_%d' % i) for i in range(positions)]
start_vars = [Int('start_%d' % i) for i in range(positions)]
end_vars = [Int('end_%d' % i) for i in range(positions)]
location_vars = [Int('location_%d' % i) for i in range(positions)]

# Add basic constraints for friend variables
for i in range(positions):
    solver.add(Or(friend_vars[i] == -1, And(friend_vars[i] >= 0, friend_vars[i] <= 8)))

# Add constraints for location based on friend
for i in range(positions):
    for friend_idx in range(9):
        solver.add(Implies(friend_vars[i] == friend_idx, location_vars[i] == friend_locations[friend_idx]))

# Helper functions to generate available_start, available_end, and duration expressions
def get_available_start_expr(friend_var):
    expr = 0
    for idx in range(9):
        expr = If(friend_var == idx, friend_available_start[idx], expr)
    return expr

def get_available_end_expr(friend_var):
    expr = 0
    for idx in range(9):
        expr = If(friend_var == idx, friend_available_end[idx], expr)
    return expr

def get_duration_expr(friend_var):
    expr = 0
    for idx in range(9):
        expr = If(friend_var == idx, friend_durations[idx], expr)
    return expr

# Add constraints for start and end times
for i in range(positions):
    available_start = get_available_start_expr(friend_vars[i])
    available_end = get_available_end_expr(friend_vars[i])
    duration = get_duration_expr(friend_vars[i])
    solver.add(Implies(friend_vars[i] != -1, 
                       And(
                           start_vars[i] >= available_start,
                           end_vars[i] == start_vars[i] + duration,
                           end_vars[i] <= available_end
                       )))

# Add constraints for first used position
for i in range(positions):
    first_used = And([friend_vars[j] == -1 for j in range(i)])
    first_used = And(first_used, friend_vars[i] != -1)
    solver.add(Implies(first_used, start_vars[i] >= 540 + travel_time[0][location_vars[i]]))

# Add constraints for subsequent positions
for i in range(1, positions):
    solver.add(Implies(friend_vars[i] != -1, 
                       start_vars[i] >= end_vars[i-1] + travel_time[location_vars[i-1]][location_vars[i]]))

# Add uniqueness constraints for friends
for i in range(positions):
    for j in range(i+1, positions):
        solver.add(Implies(And(friend_vars[i] != -1, friend_vars[j] != -1), friend_vars[i] != friend_vars[j]))

# Maximize the number of friends visited
num_friends = Sum([If(friend_vars[i] != -1, 1, 0) for i in range(positions)])
solver.maximize(num_friends)

# Check for a solution
result = solver.check()
if result == sat:
    model = solver.model()
    itinerary = []
    for i in range(positions):
        friend = model.evaluate(friend_vars[i])
        if friend != -1:
            start = model.evaluate(start_vars[i])
            end = model.evaluate(end_vars[i])
            name = friends[friend]['name']
            # Convert start and end to HH:MM format
            start_h = start.as_long() // 60
            start_m = start.as_long() % 60
            end_h = end.as_long() // 60
            end_m = end.as_long() % 60
            start_time = f"{start_h:02d}:{start_m:02d}"
            end_time = f"{end_h:02d}:{end_m:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")