from z3 import Int, Solver, If

people_travel_time = [
    [1, 2, 3, 4],
    [5, 6, 7, 8],
    [9, 10, 11, 12],
    [13, 14, 15, 16]
]

# Example symbolic variables
prev_p = Int('prev_p')
curr_p = Int('curr_p')

# Manually construct the travel time expression using nested If statements
travel_time_expr = If(prev_p == 0,
    If(curr_p == 0, 1,
       If(curr_p == 1, 2,
          If(curr_p == 2, 3,
             If(curr_p == 3, 4, 0)))),  # default for invalid curr_p
    If(prev_p == 1,
       If(curr_p == 0, 5,
          If(curr_p == 1, 6,
             If(curr_p == 2, 7,
                If(curr_p == 3, 8, 0)))),  # default
       If(prev_p == 2,
          If(curr_p == 0, 9,
             If(curr_p == 1, 10,
                If(curr_p == 2, 11,
                   If(curr_p == 3, 12, 0)))),  # default
          If(prev_p == 3,
             If(curr_p == 0, 13,
                If(curr_p == 1, 14,
                   If(curr_p == 2, 15,
                      If(curr_p == 3, 16, 0)))),  # default
             0)))))  # default for invalid prev_p

# Example: Add constraints and solve
s = Solver()
s.add(prev_p == 2, curr_p == 3)
s.check()
print(s.model()[travel_time_expr])