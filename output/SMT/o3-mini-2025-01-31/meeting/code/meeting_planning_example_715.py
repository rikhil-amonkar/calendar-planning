from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define location indices:
# 0: Presidio         (starting point)
# 1: Marina District
# 2: The Castro
# 3: Fisherman's Wharf
# 4: Bayview
# 5: Pacific Heights
# 6: Mission District
# 7: Alamo Square
# 8: Golden Gate Park

# Travel distances (in minutes) between locations.
# Each key (i, j) represents the travel time from location i to location j.
travel = {
    # From Presidio (0)
    (0,1): 11, (0,2): 21, (0,3): 19, (0,4): 31, (0,5): 11, (0,6): 26, (0,7): 19, (0,8): 12,
    # From Marina District (1)
    (1,0): 10, (1,2): 22, (1,3): 10, (1,4): 27, (1,5): 7,  (1,6): 20, (1,7): 15, (1,8): 18,
    # From The Castro (2)
    (2,0): 20, (2,1): 21, (2,3): 24, (2,4): 19, (2,5): 16, (2,6): 7,  (2,7): 8,  (2,8): 11,
    # From Fisherman's Wharf (3)
    (3,0): 17, (3,1): 9,  (3,2): 27, (3,4): 25, (3,5): 12, (3,6): 22, (3,7): 21, (3,8): 25,
    # From Bayview (4)
    (4,0): 32, (4,1): 27, (4,2): 19, (4,3): 25, (4,5): 23, (4,6): 13, (4,7): 16, (4,8): 22,
    # From Pacific Heights (5)
    (5,0): 11, (5,1): 6,  (5,2): 16, (5,3): 13, (5,4): 22, (5,6): 15, (5,7): 10, (5,8): 15,
    # From Mission District (6)
    (6,0): 25, (6,1): 19, (6,2): 7,  (6,3): 22, (6,4): 14, (6,5): 16, (6,7): 11, (6,8): 17,
    # From Alamo Square (7)
    (7,0): 17, (7,1): 15, (7,2): 8,  (7,3): 19, (7,4): 16, (7,5): 10, (7,6): 10, (7,8): 9,
    # From Golden Gate Park (8)
    (8,0): 11, (8,1): 16, (8,2): 13, (8,3): 24, (8,4): 23, (8,5): 16, (8,6): 17, (8,7): 9
}

# Friend meeting information.
# Each tuple represents:
#   (location, available_start, available_end, minimum_meeting_duration)
# Times are in minutes after midnight.
# Locations are by index in the list above.
#
# Amanda   at Marina District (1): from 2:45PM (885) to 7:30PM (1170), min 105 minutes.
# Melissa  at The Castro (2):         from 9:30AM (570) to 5:00PM (1020), min 30 minutes.
# Jeffrey  at Fisherman's Wharf (3):   from 12:45PM (765) to 6:45PM (1125), min 120 minutes.
# Matthew  at Bayview (4):             from 10:15AM (615) to 1:15PM (795), min 30 minutes.
# Nancy    at Pacific Heights (5):     from 5:00PM (1020) to 9:30PM (1290), min 105 minutes.
# Karen    at Mission District (6):      from 5:30PM (1050) to 8:30PM (1230), min 105 minutes.
# Robert   at Alamo Square (7):         from 11:15AM (675) to 5:30PM (1050), min 120 minutes.
# Joseph   at Golden Gate Park (8):       from 8:30AM (510) to 9:15PM (1275), min 105 minutes.
friends = [
    (1, 885, 1170, 105),  # Amanda
    (2, 570, 1020, 30),    # Melissa
    (3, 765, 1125, 120),   # Jeffrey
    (4, 615, 795, 30),     # Matthew
    (5, 1020, 1290, 105),  # Nancy
    (6, 1050, 1230, 105),  # Karen
    (7, 675, 1050, 120),   # Robert
    (8, 510, 1275, 105)    # Joseph
]
num_friends = len(friends)

# You arrive at Presidio (location 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create the Optimize instance.
opt = Optimize()

# Decision variables:
# x[i]: Boolean variable that is True if you decide to meet friend i.
# A[i]: Arrival time (in minutes) at friend i's location.
# order[i]: The meeting order if friend i is scheduled; if not scheduled set to -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If friend i is met, then order[i] is in the range 0 to num_friends-1; otherwise, force order[i] to be -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# If two friends are both scheduled, they must have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability and duration constraints:
# For friend i if met, we must start the meeting no earlier than their available start.
# Let effective_start = max(A[i], available_start). Then effective_start + meeting_duration must
# be no later than available_end.
for i in range(num_friends):
    loc, avail_start, avail_end, meet_min = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + meet_min <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), the travel is from the starting location (Presidio).
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j is scheduled immediately after friend i then:
# The arrival time at friend j must be at least the departure time from friend i plus the travel time.
# Define departure time from friend i as: max(A[i], available_start of friend i) + meeting duration.
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

# Solve and display the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    chosen = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            chosen.append((model.evaluate(order[i]).as_long(), i))
    chosen.sort()  # sort by meeting order

    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"

    friend_names = ["Amanda", "Melissa", "Jeffrey", "Matthew", "Nancy", "Karen", "Robert", "Joseph"]
    loc_names = {
        0: "Presidio",
        1: "Marina District",
        2: "The Castro",
        3: "Fisherman's Wharf",
        4: "Bayview",
        5: "Pacific Heights",
        6: "Mission District",
        7: "Alamo Square",
        8: "Golden Gate Park"
    }
    
    for ord_val, i in chosen:
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