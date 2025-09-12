import z3

# Assume the rest of the code defines:
# - friends: a list of dictionaries with keys like 'available_start', 'available_end', 'min_duration'
# - friends_var: a list of Z3 Int variables
# - arrival_time: a list of Z3 Int variables
# - start_time: a list of Z3 Int variables
# - end_time: a list of Z3 Int variables
# - solver: a Z3 solver object initialized with solver = z3.Solver()

# Add constraints for start and end times
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

# Add the constraints using the expressions
solver.add(z3.If(friends_var[i] != -1, start_time[i] >= arrival_time[i], True))
solver.add(z3.If(friends_var[i] != -1, end_time[i] >= start_time[i] + min_duration_expr, True))
solver.add(z3.If(friends_var[i] != -1, end_time[i] <= available_end_expr, True))
solver.add(z3.If(friends_var[i] != -1, start_time[i] >= available_start_expr, True))