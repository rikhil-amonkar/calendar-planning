import z3

# Define the list of friends with their availability and preferences
friends = [
    {'available_start': 9, 'available_end': 17, 'min_duration': 2},
    {'available_start': 10, 'available_end': 18, 'min_duration': 3},
    {'available_start': 8, 'available_end': 16, 'min_duration': 1},
    {'available_start': 11, 'available_end': 19, 'min_duration': 2}
]

# Create Z3 variables for each friend
num_friends = 4
friends_var = [z3.Int(f'friend_{i}') for i in range(num_friends)]
arrival_time = [z3.Int(f'arrival_{i}') for i in range(num_friends)]
start_time = [z3.Int(f'start_{i}') for i in range(num_friends)]
end_time = [z3.Int(f'end_{i}') for i in range(num_friends)]

# Initialize Z3 solver
solver = z3.Solver()

# Add constraints for each friend
for i in range(num_friends):
    available_start_expr = z3.If(friends_var[i] == 0, friends[0]['available_start'],
                             z3.If(friends_var[i] == 1, friends[1]['available_start'],
                                   z3.If(friends_var[i] == 2, friends[2]['available_start'],
                                         z3.If(friends_var[i] == 3, friends[3]['available_start'], 0))))

    available_end_expr = z3.If(friends_var[i] == 0, friends[0]['available_end'],
                           z3.If(friends_var[i] == 1, friends[1]['available_end'],
                                 z3.If(friends_var[i] == 2, friends[2]['available_end'],
                                       z3.If(friends_var[i] == 3, friends[3]['available_end'], 0))))

    min_duration_expr = z3.If(friends_var[i] == 0, friends[0]['min_duration'],
                          z3.If(friends_var[i] == 1, friends[1]['min_duration'],
                                z3.If(friends_var[i] == 2, friends[2]['min_duration'],
                                      z3.If(friends_var[i] == 3, friends[3]['min_duration'], 0))))

    # Add constraints
    solver.add(z3.If(friends_var[i] != -1, start_time[i] >= arrival_time[i], True))
    solver.add(z3.If(friends_var[i] != -1, end_time[i] >= start_time[i] + min_duration_expr, True))
    solver.add(z3.If(friends_var[i] != -1, end_time[i] <= available_end_expr, True))
    solver.add(z3.If(friends_var[i] != -1, start_time[i] >= available_start_expr, True))

# Check for satisfiability
result = solver.check()
print("Solver result:", result)

if result == z3.sat:
    model = solver.model()
    for i in range(num_friends):
        print(f"Friend {i}:")
        print(f"  friend_var: {model[friends_var[i]]}")
        print(f"  arrival: {model[arrival_time[i]]}")
        print(f"  start: {model[start_time[i]]}")
        print(f"  end: {model[end_time[i]]}")