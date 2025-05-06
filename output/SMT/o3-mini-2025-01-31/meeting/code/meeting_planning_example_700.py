from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    # From Presidio
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,

    # From Pacific Heights
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "North Beach"): 9,

    # From Golden Gate Park
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "North Beach"): 23,

    # From Fisherman's Wharf
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,

    # From Marina District
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "North Beach"): 11,

    # From Alamo Square
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,

    # From Sunset District
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "North Beach"): 28,

    # From Nob Hill
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "North Beach"): 8,

    # From North Beach
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Nob Hill"): 7
}

# Define friend meeting details.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration), where times are in minutes after midnight.
friends = [
    # Kevin: at Pacific Heights from 7:15AM to 8:45AM; meeting >= 90 minutes.
    ("Pacific Heights", 435, 525, 90),
    # Michelle: at Golden Gate Park from 8:00PM to 9:00PM; meeting >= 15 minutes.
    ("Golden Gate Park", 1200, 1260, 15),
    # Emily: at Fisherman's Wharf from 4:15PM to 7:00PM; meeting >= 30 minutes.
    ("Fisherman's Wharf", 975, 1140, 30),
    # Mark: at Marina District from 6:15PM to 7:45PM; meeting >= 75 minutes.
    ("Marina District", 1095, 1185, 75),
    # Barbara: at Alamo Square from 5:00PM to 7:00PM; meeting >= 120 minutes.
    ("Alamo Square", 1020, 1140, 120),
    # Laura: at Sunset District from 7:00PM to 9:15PM; meeting >= 75 minutes.
    ("Sunset District", 1140, 1275, 75),
    # Mary: at Nob Hill from 5:30PM to 7:00PM; meeting >= 45 minutes.
    ("Nob Hill", 1050, 1140, 45),
    # Helen: at North Beach from 11:00AM to 12:15PM; meeting >= 45 minutes.
    ("North Beach", 660, 735, 45)
]

friend_names = ["Kevin", "Michelle", "Emily", "Mark", "Barbara", "Laura", "Mary", "Helen"]
num_friends = len(friends)

# Starting conditions:
# You arrive at Presidio at 9:00AM (540 minutes after midnight)
start_loc = "Presidio"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, create decision variables:
# x[i]: a Bool indicating whether you schedule a meeting with friend i.
# A[i]: an Int representing the arrival time at friend i’s location.
# order[i]: an Int representing the order in which friend i is visited (0 ... num_friends-1 if scheduled, -1 if not).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled, order is between 0 and num_friends-1. Otherwise, it is forced to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct order positions.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# If meeting with friend i is scheduled, the meeting starts at the later of arrival time A[i] and the friend's avail_start.
# The meeting then lasts for the required duration and must complete by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), you travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings:
# If friend j immediately follows friend i (order[j] == order[i] + 1),
# then you must have enough time to travel from friend i's location to friend j.
# Define departure time from friend i as meeting_start (max(A[i], avail_start)) plus the meeting duration.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + t_time))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and print the optimal meeting schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings and order them by their scheduled order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Function to convert minutes after midnight to HH:MM format.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting starts at max(arrival, avail_start)
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")