from z3 import *

# Travel time matrix (10x10)
# Index: 0: Union Square, 1: The Castro, 2: North Beach, 3: Embarcadero, 4: Alamo Square, 
#         5: Nob Hill, 6: Presidio, 7: Fisherman's Wharf, 8: Mission District, 9: Haight-Ashbury
T = [
    [0, 17, 10, 11, 15, 9, 24, 15, 14, 18],   # Union Square
    [19, 0, 20, 22, 8, 16, 20, 24, 7, 6],      # The Castro
    [7, 23, 0, 6, 16, 7, 17, 5, 18, 18],       # North Beach
    [10, 25, 5, 0, 19, 10, 20, 6, 20, 21],     # Embarcadero
    [14, 8, 15, 16, 0, 11, 17, 19, 10, 5],     # Alamo Square
    [7, 17, 8, 9, 11, 0, 17, 10, 13, 13],      # Nob Hill
    [22, 21, 18, 20, 19, 18, 0, 19, 26, 15],   # Presidio
    [13, 27, 6, 8, 21, 11, 17, 0, 22, 22],     # Fisherman's Wharf
    [15, 7, 17, 19, 11, 12, 25, 22, 0, 12],    # Mission District
    [19, 6, 19, 20, 5, 15, 15, 23, 11, 0]      # Haight-Ashbury
]

# Meeting data: for each meeting location (index 1 to 9) we have (start_min, end_min, min_time)
# Times are in minutes from 9:00 AM
meeting_data = {
    1: (675, 735, 30),   # Melissa at The Castro (8:15PM to 9:15PM -> 11.25 to 12.25 hours from 9AM -> 675 to 735 minutes)
    2: (0, 90, 15),       # Kimberly at North Beach (7:00AM to 10:30AM -> 9:00AM to 10:30AM is 0 to 90 minutes)
    3: (390, 630, 75),    # Joseph at Embarcadero (3:30PM to 7:30PM -> 6.5 to 10.5 hours from 9AM -> 390 to 630 minutes)
    4: (705, 765, 15),    # Barbara at Alamo Square (8:45PM to 9:45PM -> 705 to 765 minutes)
    5: (195, 495, 105),   # Kenneth at Nob Hill (12:15PM to 5:15PM -> 3.25 to 8.25 hours from 9AM -> 195 to 495 minutes)
    6: (450, 555, 105),   # Joshua at Presidio (4:30PM to 6:15PM -> 7.5 to 9.25 hours from 9AM -> 450 to 555 minutes)
    7: (30, 390, 45),     # Brian at Fisherman's Wharf (9:30AM to 3:30PM -> 0.5 to 6.5 hours from 9AM -> 30 to 390 minutes)
    8: (630, 720, 90),    # Steven at Mission District (7:30PM to 9:00PM -> 10.5 to 12 hours from 9AM -> 630 to 720 minutes)
    9: (600, 690, 90)     # Betty at Haight-Ashbury (7:00PM to 8:30PM -> 10 to 11.5 hours from 9AM -> 600 to 690 minutes)
}

# Create solver
s = Solver()
# Set to not produce verbose output
set_option("verbose", 0)

# Big M value
M = 10000

# y_i: whether we meet friend at location i (for i in 1..9)
y = [Bool(f"y_{i}") for i in range(1, 10)]

# p[i][j]: whether we travel from node i to node j
# i in [0,1,...,9] and j in [1,2,...,10] (j=10 is the dummy end node)
p = {}
for i in range(0, 10):
    for j in range(1, 11):
        p[(i, j)] = Bool(f"p_{i}_{j}")

# a_i: arrival time at meeting i (for i in 1..9)
a = [Real(f"a_{i}") for i in range(1, 10)]

# s_i: start time of meeting i (for i in 1..9)
s_time = [Real(f"s_{i}") for i in range(1, 10)]

# d_i: departure time from meeting i (for i in 1..9)
d = [Real(f"d_{i}") for i in range(1, 10)]

# u_i: position in the path for meeting i (for i in 1..9)
u = [Int(f"u_{i}") for i in range(1, 10)]

# Constraint (1): Start node (0) has exactly one outgoing edge to a meeting or end
s.add(Sum([If(p[(0, j)], 1, 0) for j in range(1, 11)]) == 1)

# Constraint (2): For each meeting i (1..9), if y_i is true, then exactly one outgoing edge
for i in range(1, 10):
    s.add(If(y[i-1], 
            Sum([If(p[(i, j)], 1, 0) for j in range(1, 11)]) == 1, 
            Sum([If(p[(i, j)], 1, 0) for j in range(1, 11)]) == 0))

# Constraint (3): For each meeting j (1..9), if y_j is true, then exactly one incoming edge
for j in range(1, 10):
    incoming_from_start = p[(0, j)]
    incoming_from_meetings = [p[(i, j)] for i in range(1, 10)]
    s.add(If(y[j-1], 
            incoming_from_start + Sum([If(inc, 1, 0) for inc in incoming_from_meetings]) == 1, 
            incoming_from_start + Sum([If(inc, 1, 0) for inc in incoming_from_meetings]) == 0))

# Constraint (4): Arrival time constraints
# For the start to meeting j
for j in range(1, 10):
    # Travel time from start (0) to meeting j: T[0][j]
    s.add(If(p[(0, j)], a[j-1] == T[0][j], True))

# For meeting i to meeting j
for i in range(1, 10):
    for j in range(1, 10):
        if i != j:
            # If we go from i to j, then a_j >= d_i + T[i][j]
            s.add(If(p[(i, j)], 
                    a[j-1] >= d[i-1] + T[i][j], 
                    True))
    # For meeting i to end (j=10): no constraint

# Constraint (5): Meeting time constraints for each meeting i
for i in range(1, 10):
    start_i = meeting_data[i][0]
    end_i = meeting_data[i][1]
    min_time_i = meeting_data[i][2]
    # s_i >= max(a_i, start_i) -> split
    s.add(If(y[i-1], 
            And(
                s_time[i-1] >= a[i-1],
                s_time[i-1] >= start_i,
                s_time[i-1] <= end_i - min_time_i
            ), 
            True))
    # d_i = s_i + min_time_i
    s.add(If(y[i-1], d[i-1] == s_time[i-1] + min_time_i, True))

# Constraint (6): MTZ for no subtours
# For the start to meeting j: if we go from start to j, then u_j = 1
for j in range(1, 10):
    s.add(If(p[(0, j)], u[j-1] == 1, True))

# For meeting i to meeting j: if we go from i to j, then u_j = u_i + 1
for i in range(1, 10):
    for j in range(1, 10):
        if i != j:
            s.add(If(p[(i, j)], u[j-1] == u[i-1] + 1, True))

# Also, if a meeting is not selected, we set u_i to 0? But we don't care. 
# We can bound u_i: if selected, u_i >=1, else u_i >=0 and we don't care.
for i in range(1, 10):
    s.add(If(y[i-1], u[i-1] >= 1, u[i-1] >= 0))
    s.add(u[i-1] <= 10)  # at most 9 meetings, so position <=9, but we set 10

# Constraint (7): If an arc is taken, then the meetings at both ends must be selected (for meetings) or for the start, the destination must be selected.
for j in range(1, 10):
    s.add(If(p[(0, j)], y[j-1], True))

for i in range(1, 10):
    for j in range(1, 10):
        if i != j:
            s.add(If(p[(i, j)], And(y[i-1], y[j-1]), True))
    s.add(If(p[(i, 10)], y[i-1], True))

# Objective: maximize the number of meetings
obj = Sum([If(y_i, 1, 0) for y_i in y])
s.maximize(obj)

# Solve
result = s.check()
if result == sat:
    m = s.model()
    total_meetings = 0
    schedule = []
    friend_names = {
        1: "Melissa", 2: "Kimberly", 3: "Joseph", 4: "Barbara", 
        5: "Kenneth", 6: "Joshua", 7: "Brian", 8: "Steven", 9: "Betty"
    }
    # Collect the order from u_i
    order_list = []
    for i in range(1, 10):
        if m.evaluate(y[i-1]):
            total_meetings += 1
            u_val = m.evaluate(u[i-1])
            if is_int_value(u_val):
                pos = u_val.as_long()
            else:
                pos = int(str(u_val))
            order_list.append((pos, friend_names[i], i))
    order_list.sort(key=lambda x: x[0])
    # Print the solution
    print("SOLUTION:")
    print(f"Total meetings: {total_meetings}")
    print("Schedule in order:")
    for pos, name, loc in order_list:
        s_time_val = m.evaluate(s_time[loc-1])
        # Convert to time string
        if is_rational_value(s_time_val):
            minutes = s_time_val.as_fraction()
            total_minutes = float(minutes)
        elif is_algebraic_value(s_time_val):
            total_minutes = float(s_time_val.approx(5).as_decimal(5))
        else:
            total_minutes = float(str(s_time_val))
        hours = int(total_minutes // 60)
        mins = int(total_minutes % 60)
        start_hour = 9 + hours
        start_minute = mins
        am_pm = "AM"
        if start_hour >= 12:
            am_pm = "PM"
            if start_hour > 12:
                start_hour -= 12
        start_str = f"{start_hour}:{start_minute:02d} {am_pm}"
        print(f"  Meet {name} at location {loc} starting at {start_str} (position {pos})")
else:
    print("No solution found")