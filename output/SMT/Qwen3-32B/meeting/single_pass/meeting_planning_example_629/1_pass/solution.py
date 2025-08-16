import z3
import json

# Define friends' data
friends_data = [
    {'name': 'Matthew', 'available_start': 660, 'available_end': 1260, 'duration': 90},
    {'name': 'Margaret', 'available_start': 555, 'available_end': 1005, 'duration': 90},
    {'name': 'Nancy', 'available_start': 855, 'available_end': 900, 'duration': 15},
    {'name': 'Helen', 'available_start': 1185, 'available_end': 1320, 'duration': 60},
    {'name': 'Rebecca', 'available_start': 1275, 'available_end': 1335, 'duration': 60},
    {'name': 'Kimberly', 'available_start': 780, 'available_end': 990, 'duration': 120},
    {'name': 'Kenneth', 'available_start': 870, 'available_end': 1080, 'duration': 60},
]

friend_to_location = [1, 2, 3, 4, 5, 6, 7]

# Travel times matrix
travel_times = [
    [0, 14, 9, 7, 14, 7, 21, 23],
    [14, 0, 21, 11, 7, 19, 12, 31],
    [7, 19, 0, 10, 20, 8, 23, 22],
    [7, 11, 10, 0, 12, 13, 15, 22],
    [13, 7, 20, 10, 0, 18, 9, 26],
    [7, 17, 12, 12, 18, 0, 25, 26],
    [19, 11, 23, 16, 7, 24, 0, 23],
    [23, 31, 18, 23, 25, 25, 22, 0]
]

# Z3 setup
solver = z3.Optimize()

max_steps = 7
friends = [z3.Int(f'friend_{i}') for i in range(max_steps)]
starts = [z3.Int(f'start_{i}') for i in range(max_steps)]
ends = [z3.Int(f'end_{i}') for i in range(max_steps)]
locations = [z3.Int(f'location_{i}') for i in range(max_steps)]

# Initial step (i=0)
solver.add(friends[0] == -1)
solver.add(starts[0] == 540)
solver.add(ends[0] == 540)
solver.add(locations[0] == 0)

# Constraints for each step i >= 1
for i in range(1, max_steps):
    prev_end = ends[i-1]
    prev_location = locations[i-1]
    current_friend = friends[i]
    current_start = starts[i]
    current_end = ends[i]
    current_location = locations[i]

    # Determine current_location based on current_friend
    current_loc_expr = z3.If(current_friend == 0, 1,
                             z3.If(current_friend == 1, 2,
                                   z3.If(current_friend == 2, 3,
                                         z3.If(current_friend == 3, 4,
                                               z3.If(current_friend == 4, 5,
                                                     z3.If(current_friend == 5, 6,
                                                           z3.If(current_friend == 6, 7, 0)))))))
    current_loc_expr = z3.If(current_friend != -1, current_loc_expr, prev_location)
    solver.add(current_location == current_loc_expr)

    # Travel time between prev_location and current_location
    travel_time_expr = z3.If(prev_location == 0,
                             z3.If(current_location == 0, 0,
                                   z3.If(current_location == 1, 14,
                                         z3.If(current_location == 2, 9,
                                               z3.If(current_location == 3, 7,
                                                     z3.If(current_location == 4, 14,
                                                           z3.If(current_location == 5, 7,
                                                                 z3.If(current_location == 6, 21,
                                                                       z3.If(current_location == 7, 23, 0))))))),
                             z3.If(prev_location == 1,
                                   z3.If(current_location == 0, 14,
                                         z3.If(current_location == 1, 0,
                                               z3.If(current_location == 2, 21,
                                                     z3.If(current_location == 3, 11,
                                                           z3.If(current_location == 4, 7,
                                                                 z3.If(current_location == 5, 19,
                                                                       z3.If(current_location == 6, 12,
                                                                             z3.If(current_location == 7, 31, 0))))))),
                                   z3.If(prev_location == 2,
                                         z3.If(current_location == 0, 7,
                                               z3.If(current_location == 1, 19,
                                                     z3.If(current_location == 2, 0,
                                                           z3.If(current_location == 3, 10,
                                                                 z3.If(current_location == 4, 20,
                                                                       z3.If(current_location == 5, 8,
                                                                             z3.If(current_location == 6, 23,
                                                                                   z3.If(current_location == 7, 22, 0))))))),
                                         z3.If(prev_location == 3,
                                               z3.If(current_location == 0, 7,
                                                     z3.If(current_location == 1, 11,
                                                           z3.If(current_location == 2, 10,
                                                                 z3.If(current_location == 3, 0,
                                                                       z3.If(current_location == 4, 12,
                                                                             z3.If(current_location == 5, 13,
                                                                                   z3.If(current_location == 6, 15,
                                                                                         z3.If(current_location == 7, 22, 0))))))),
                                               z3.If(prev_location == 4,
                                                     z3.If(current_location == 0, 13,
                                                           z3.If(current_location == 1, 7,
                                                                 z3.If(current_location == 2, 20,
                                                                       z3.If(current_location == 3, 10,
                                                                             z3.If(current_location == 4, 0,
                                                                                   z3.If(current_location == 5, 18,
                                                                                         z3.If(current_location == 6, 9,
                                                                                               z3.If(current_location == 7, 26, 0))))))),
                                                     z3.If(prev_location == 5,
                                                           z3.If(current_location == 0, 7,
                                                                 z3.If(current_location == 1, 17,
                                                                       z3.If(current_location == 2, 12,
                                                                             z3.If(current_location == 3, 12,
                                                                                   z3.If(current_location == 4, 18,
                                                                                         z3.If(current_location == 5, 0,
                                                                                               z3.If(current_location == 6, 25,
                                                                                                     z3.If(current_location == 7, 26, 0))))))),
                                                           z3.If(prev_location == 6,
                                                                 z3.If(current_location == 0, 19,
                                                                       z3.If(current_location == 1, 11,
                                                                             z3.If(current_location == 2, 23,
                                                                                   z3.If(current_location == 3, 16,
                                                                                         z3.If(current_location == 4, 7,
                                                                                               z3.If(current_location == 5, 24,
                                                                                                     z3.If(current_location == 6, 0,
                                                                                                           z3.If(current_location == 7, 23, 0))))))),
                                                                 z3.If(prev_location == 7,
                                                                       z3.If(current_location == 0, 23,
                                                                             z3.If(current_location == 1, 31,
                                                                                   z3.If(current_location == 2, 18,
                                                                                         z3.If(current_location == 3, 23,
                                                                                               z3.If(current_location == 4, 25,
                                                                                                     z3.If(current_location == 5, 25,
                                                                                                           z3.If(current_location == 6, 22,
                                                                                                                 z3.If(current_location == 7, 0, 0))))))),
                                                                       0))))))
    solver.add(z3.Implies(current_friend != -1, current_start >= prev_end + travel_time_expr))

    # Available start time
    solver.add(z3.Implies(current_friend != -1, current_start >= friends_data[current_friend]['available_start']))

    # End time
    solver.add(z3.Implies(current_friend != -1, current_end == current_start + friends_data[current_friend]['duration']))

    # Available end time
    solver.add(z3.Implies(current_friend != -1, current_end <= friends_data[current_friend]['available_end']))

    # If no meeting, same as previous
    solver.add(z3.Implies(current_friend == -1, current_start == prev_end))
    solver.add(z3.Implies(current_friend == -1, current_end == prev_end))
    solver.add(z3.Implies(current_friend == -1, current_location == prev_location))

# Ensure no duplicate friends
for i in range(max_steps):
    for j in range(i+1, max_steps):
        solver.add(z3.Or(friends[i] == -1, friends[j] == -1, friends[i] != friends[j]))

# Objective: maximize friends visited
num_friends_visited = sum([z3.If(friends[i] != -1, 1, 0) for i in range(max_steps)])
solver.maximize(num_friends_visited)

# Solve and extract solution
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(max_steps):
        f = model.eval(friends[i])
        if f != -1:
            start = model.eval(starts[i]).as_long()
            end = model.eval(ends[i]).as_long()
            person = friends_data[f]['name']
            start_time = f"{(start // 60):02d}:{(start % 60):02d}"
            end_time = f"{(end // 60):02d}:{(end % 60):02d}"
            itinerary.append({"action": "meet", "person": person, "start_time": start_time, "end_time": end_time})
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")