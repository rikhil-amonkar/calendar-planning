from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Location indices:
# 0: Haight-Ashbury    (starting point)
# 1: Russian Hill
# 2: Fisherman's Wharf
# 3: Nob Hill
# 4: Golden Gate Park
# 5: Alamo Square
# 6: Pacific Heights

# Travel distances (in minutes) between the locations.
# Each key (i, j) denotes the travel time from location i to location j.
travel = {
    (0,1): 17, (0,2): 23, (0,3): 15, (0,4): 7,  (0,5): 5,  (0,6): 12,
    (1,0): 17, (1,2): 7,  (1,3): 5,  (1,4): 21, (1,5): 15, (1,6): 7,
    (2,0): 22, (2,1): 7,  (2,3): 11, (2,4): 25, (2,5): 20, (2,6): 12,
    (3,0): 13, (3,1): 5,  (3,2): 11, (3,4): 17, (3,5): 11, (3,6): 8,
    (4,0): 7,  (4,1): 19, (4,2): 24, (4,3): 20, (4,5): 10, (4,6): 16,
    (5,0): 5,  (5,1): 13, (5,2): 19, (5,3): 11, (5,4): 9,  (5,6): 10,
    (6,0): 11, (6,1): 7,  (6,2): 13, (6,3): 8,  (6,4): 15, (6,5): 10
}

# Friend meeting information.
# Each tuple contains:
#   (location, available_start, available_end, minimum_meeting_duration)
# All times are in minutes after midnight.
#
# Stephanie at Russian Hill (loc 1): 8:00PM to 8:45PM (1200 to 1245), min 15 minutes.
# Kevin     at Fisherman's Wharf (loc 2): 7:15PM to 9:45PM (1155 to 1305), min 75 minutes.
# Robert    at Nob Hill (loc 3): 7:45AM to 10:30AM (465 to 630), min 90 minutes.
# Steven    at Golden Gate Park (loc 4): 8:30AM to 5:00PM (510 to 1020), min 75 minutes.
# Anthony   at Alamo Square (loc 5): 7:45AM to 7:45PM (465 to 1185), min 15 minutes.
# Sandra    at Pacific Heights (loc 6): 2:45PM to 9:45PM (885 to 1305), min 45 minutes.
friends = [
    (1, 1200, 1245, 15),  # Stephanie
    (2, 1155, 1305, 75),  # Kevin
    (3, 465, 630, 90),    # Robert
    (4, 510, 1020, 75),   # Steven
    (5, 465, 1185, 15),   # Anthony
    (6, 885, 1305, 45)    # Sandra
]
num_friends = len(friends)

# You arrive at Haight-Ashbury (location 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create an Optimize instance.
opt = Optimize()

# Decision variables:
# x[i]: Boolean that is True if you meet friend i.
# A[i]: Arrival time (in minutes) at friend i's location.
# order[i]: Integer representing the meeting order if scheduled; if not scheduled, we force order[i] to be -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend i, if meeting is chosen then order[i] is between 0 and num_friends-1; otherwise order[i] is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that if two friends are met, they have distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# For a met friend i, define effective_start = max(A[i], available_start).
# Then effective_start + meeting duration must be <= available_end.
for i in range(num_friends):
    loc, avail_start, avail_end, meet_min = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + meet_min <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), ensure the arrival time A[i] respects travel time from starting point.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j is scheduled immediately after friend i then
# the arrival time at j must be at least the departure time from i plus the travel time.
# Define departure time from i as: max(A[i], available_start_i) + meeting duration.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, meet_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + meet_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time))

# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and print the optimal meeting schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by meeting order

    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Stephanie", "Kevin", "Robert", "Steven", "Anthony", "Sandra"]
    loc_names = {
        0: "Haight-Ashbury",
        1: "Russian Hill",
        2: "Fisherman's Wharf",
        3: "Nob Hill",
        4: "Golden Gate Park",
        5: "Alamo Square",
        6: "Pacific Heights"
    }
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, meet_min = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + meet_min
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc_names[loc]}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")