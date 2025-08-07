from z3 import *

# Define travel time matrix (11x11)
T = [
    [0, 24, 15, 18, 9, 9, 27, 7, 13, 10, 18],
    [22, 0, 19, 11, 23, 18, 15, 21, 14, 18, 15],
    [14, 17, 0, 15, 17, 11, 16, 15, 13, 15, 5],
    [16, 10, 15, 0, 17, 12, 19, 15, 8, 11, 16],
    [9, 22, 17, 15, 0, 8, 30, 5, 11, 7, 19],
    [7, 17, 11, 11, 9, 0, 24, 6, 5, 8, 13],
    [30, 16, 17, 21, 30, 27, 0, 30, 24, 28, 15],
    [7, 19, 17, 12, 5, 9, 29, 0, 7, 3, 19],
    [10, 14, 15, 7, 11, 5, 23, 9, 0, 5, 17],
    [7, 17, 16, 9, 8, 7, 27, 6, 4, 0, 18],
    [19, 15, 5, 17, 21, 15, 15, 19, 17, 19, 0]
]

# Friend data: (name, location, available_start (min from 9:00), available_end (min from 9:00), min_duration)
friends = [
    ("Dummy", "Union Square", 0, 0, 0),  # Dummy meeting at start
    ("Kimberly", "Presidio", 390, 420, 15),  # 3:30PM-4:00PM
    ("Elizabeth", "Alamo Square", 615, 675, 15),  # 7:15PM-8:15PM
    ("Joshua", "Marina District", 90, 315, 45),  # 10:30AM-2:15PM
    ("Sandra", "Financial District", 630, 675, 45),  # 7:30PM-8:15PM
    ("Kenneth", "Nob Hill", 225, 765, 30),  # 12:45PM-9:45PM
    ("Betty", "Sunset District", 300, 600, 60),  # 2:00PM-7:00PM
    ("Deborah", "Chinatown", 495, 690, 15),  # 5:15PM-8:30PM
    ("Barbara", "Russian Hill", 510, 735, 120),  # 5:30PM-9:15PM
    ("Steven", "North Beach", 525, 705, 90),  # 5:45PM-8:45PM
    ("Daniel", "Haight-Ashbury", 570, 585, 15)   # 6:30PM-6:45PM
]

n = len(friends)  # 11 meetings including dummy

# Initialize Z3 optimizer
opt = Optimize()

# Meet variables for friends 1 to 10 (index 1 to 10); dummy is always met
meet = [None] * n
for i in range(1, n):
    meet[i] = Bool(f'meet_{i}')

# Start time variables for all meetings (including dummy)
start = [Int(f'start_{i}') for i in range(n)]

# Fix dummy meeting at time 0
opt.add(start[0] == 0)

# Constraints for each friend (if met, within availability and min duration)
for i in range(1, n):
    # If meeting i is held, it must start within [available_start, available_end - min_duration]
    opt.add(Implies(meet[i], start[i] >= friends[i][2]))
    opt.add(Implies(meet[i], start[i] + friends[i][4] <= friends[i][3]))

# Travel time from start (dummy at Union Square) to any meeting
for i in range(1, n):
    opt.add(Implies(meet[i], start[i] >= T[0][i]))

# Pairwise constraints for every pair of meetings (including dummy)
for i in range(n):
    for j in range(i + 1, n):
        if i == 0:  # Dummy is always met
            cond = meet[j]
        else:
            cond = And(meet[i], meet[j])
        # If both meetings are held, ensure travel time between them
        disj1 = (start[j] >= start[i] + friends[i][4] + T[i][j])
        disj2 = (start[i] >= start[j] + friends[j][4] + T[j][i])
        opt.add(Implies(cond, Or(disj1, disj2)))

# Objective: maximize number of meetings
obj = Sum([If(meet[i], 1, 0) for i in range(1, n)])
opt.maximize(obj)

# Solve and extract solution
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for i in range(1, n):
        if m.eval(meet[i]):
            s_val = m.eval(start[i])
            # Convert Z3 Int to Python int
            s_min = s_val.as_long()
            # Calculate start time in HH:MM
            total_min = s_min
            hours = 9 + total_min // 60
            minutes = total_min % 60
            start_time = f"{int(hours):02d}:{int(minutes):02d}"
            # Calculate end time
            end_min = s_min + friends[i][4]
            end_hours = 9 + end_min // 60
            end_minutes = end_min % 60
            end_time = f"{int(end_hours):02d}:{int(end_minutes):02d}"
            itinerary.append({
                "action": "meet",
                "person": friends[i][0],
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    # Output as JSON
    print({
        "itinerary": itinerary
    })
else:
    print('{"itinerary": []}')