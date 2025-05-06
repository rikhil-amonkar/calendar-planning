from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Location indices:
# 0: Union Square
# 1: Presidio
# 2: Alamo Square
# 3: Marina District
# 4: Financial District
# 5: Nob Hill
# 6: Sunset District
# 7: Chinatown
# 8: Russian Hill
# 9: North Beach
# 10: Haight-Ashbury

# Build the travel time dictionary (in minutes) from the provided data.
travel = {
    # From Union Square (0)
    (0,1):24, (0,2):15, (0,3):18, (0,4):9, (0,5):9, (0,6):27, (0,7):7, (0,8):13, (0,9):10, (0,10):18,
    # From Presidio (1)
    (1,0):22, (1,2):19, (1,3):11, (1,4):23, (1,5):18, (1,6):15, (1,7):21, (1,8):14, (1,9):18, (1,10):15,
    # From Alamo Square (2)
    (2,0):14, (2,1):17, (2,3):15, (2,4):17, (2,5):11, (2,6):16, (2,7):15, (2,8):13, (2,9):15, (2,10):5,
    # From Marina District (3)
    (3,0):16, (3,1):10, (3,2):15, (3,4):17, (3,5):12, (3,6):19, (3,7):15, (3,8):8, (3,9):11, (3,10):16,
    # From Financial District (4)
    (4,0):9, (4,1):22, (4,2):17, (4,3):15, (4,5):8, (4,6):30, (4,7):5, (4,8):11, (4,9):7, (4,10):19,
    # From Nob Hill (5)
    (5,0):7, (5,1):17, (5,2):11, (5,3):11, (5,4):9, (5,6):24, (5,7):6, (5,8):5, (5,9):8, (5,10):13,
    # From Sunset District (6)
    (6,0):30, (6,1):16, (6,2):17, (6,3):21, (6,4):30, (6,5):27, (6,7):30, (6,8):24, (6,9):28, (6,10):15,
    # From Chinatown (7)
    (7,0):7, (7,1):19, (7,2):17, (7,3):12, (7,4):5, (7,5):9, (7,6):29, (7,8):7, (7,9):3, (7,10):19,
    # From Russian Hill (8)
    (8,0):10, (8,1):14, (8,2):15, (8,3):7, (8,4):11, (8,5):5, (8,6):23, (8,7):9, (8,9):5, (8,10):17,
    # From North Beach (9)
    (9,0):7, (9,1):17, (9,2):16, (9,3):9, (9,4):8, (9,5):7, (9,6):27, (9,7):6, (9,8):4, (9,10):18,
    # From Haight-Ashbury (10)
    (10,0):19, (10,1):15, (10,2):5, (10,3):17, (10,4):21, (10,5):15, (10,6):15, (10,7):19, (10,8):17, (10,9):19
}

# Define friend meeting information.
# For friend i, we store (meeting_location, avail_start, avail_end, meeting_min)
# Times in minutes after midnight.
friends = [
    # Kimberly at Presidio (loc 1): 3:30PM (930) to 4:00PM (960), min 15
    (1, 930, 960, 15),
    # Elizabeth at Alamo Square (loc 2): 7:15PM (1155) to 8:15PM (1215), min 15
    (2, 1155, 1215, 15),
    # Joshua at Marina District (loc 3): 10:30AM (630) to 2:15PM (855), min 45
    (3, 630, 855, 45),
    # Sandra at Financial District (loc 4): 7:30PM (1170) to 8:15PM (1215), min 45
    (4, 1170, 1215, 45),
    # Kenneth at Nob Hill (loc 5): 12:45PM (765) to 9:45PM (1305), min 30
    (5, 765, 1305, 30),
    # Betty at Sunset District (loc 6): 2:00PM (840) to 7:00PM (1140), min 60
    (6, 840, 1140, 60),
    # Deborah at Chinatown (loc 7): 5:15PM (1035) to 8:30PM (1230), min 15
    (7, 1035, 1230, 15),
    # Barbara at Russian Hill (loc 8): 5:30PM (1050) to 9:15PM (1275), min 120
    (8, 1050, 1275, 120),
    # Steven at North Beach (loc 9): 5:45PM (1065) to 8:45PM (1245), min 90
    (9, 1065, 1245, 90),
    # Daniel at Haight-Ashbury (loc 10): 6:30PM (1110) to 6:45PM (1125), min 15
    (10, 1110, 1125, 15)
]
num_friends = len(friends)

# Start location and start time.
start_loc = 0  # Union Square
start_time = 540  # 9:00AM

opt = Optimize()

# Decision variables:
# For each friend i, x[i] is True if you choose to meet them.
# A[i] is the (arrival) time at friend i's location.
# order[i] is the position (order) in the itinerary if friend i is chosen, else -1.
x = [ Bool(f"x_{i}") for i in range(num_friends) ]
A = [ Int(f"A_{i}") for i in range(num_friends) ]
order = [ Int(f"order_{i}") for i in range(num_friends) ]

for i in range(num_friends):
    # If not chosen, we set order[i] = -1.
    opt.add( Or( Not(x[i]), And(order[i] >= 0, order[i] < num_friends) ) )
    opt.add( Or( Not(x[i]), True, ) )  # Just to have option for x[i] true.
    # Enforce: if not chosen then order is -1.
    opt.add( If(x[i], True, order[i] == -1) )
    # Arrival time must be nonnegative.
    opt.add( A[i] >= 0 )

# For any two friends that are chosen, they must get different order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add( Or( Not(x[i]), Not(x[j]), order[i] != order[j] ) )

# Meeting availability constraints.
for i in range(num_friends):
    loc, avail_start, avail_end, meet_req = friends[i]
    # Effective meeting start is the later of the arrival time and avail_start.
    eff_start = If(A[i] < avail_start, avail_start, A[i])
    # If meeting is held, then finishing the meeting must be no later than avail_end.
    opt.add( Or( Not(x[i]), eff_start + meet_req <= avail_end ) )

# Travel constraints:
# For a friend that is visited first (order==0) we must travel from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_travel = travel[(start_loc, loc)]
    opt.add( Or( Not(x[i]), order[i] != 0, A[i] >= start_time + t_travel ) )

# For every two different friends, if friend j is scheduled immediately after friend i in the itinerary,
# then the arrival time at j must be at least the departure time from i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, meet_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        # Effective departure from friend i: meeting starts at max(A_i, avail_start_i) and lasts meet_i.
        dep_i = If(A[i] < avail_i, avail_i, A[i]) + meet_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And( x[i], x[j], order[j] == order[i] + 1 )
        opt.add( Or( Not(cond), A[j] >= dep_i + travel_time ) )

# (Optional: Force order numbers to be contiguous among chosen ones. This is not strictly necessary.)

# Objective: maximize the number of friends met.
opt.maximize( Sum([ If(x[i], 1, 0) for i in range(num_friends) ] ) )

# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    chosen = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            chosen.append((model.evaluate(order[i]).as_long(), i))
    chosen.sort()  # sort by order
    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    for ord_val, i in chosen:
        loc, avail_start, avail_end, meet_req = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + meet_req
        loc_names = {
            0:"Union Square", 1:"Presidio", 2:"Alamo Square", 3:"Marina District",
            4:"Financial District", 5:"Nob Hill", 6:"Sunset District", 7:"Chinatown",
            8:"Russian Hill", 9:"North Beach", 10:"Haight-Ashbury"
        }
        friend_names = ["Kimberly", "Elizabeth", "Joshua", "Sandra", "Kenneth",
                        "Betty", "Deborah", "Barbara", "Steven", "Daniel"]
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc_names[loc]}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")