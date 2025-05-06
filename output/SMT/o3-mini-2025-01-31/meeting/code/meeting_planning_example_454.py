from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Note: The travel times are asymmetric.
travel = {
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Mission District"): 26,
    
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Mission District"): 13,
    
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Mission District"): 18,
    
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Mission District"): 18,
    
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "North Beach"): 17,
}

# --------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration)
#
# Times are minutes after midnight:
# Jessica:  at Golden Gate Park,    from 1:45PM to 3:00PM  (825 to 900),   min meeting = 30 minutes.
# Ashley:   at Bayview,             from 5:15PM to 8:00PM  (1035 to 1200),  min meeting = 105 minutes.
# Ronald:   at Chinatown,           from 7:15AM to 2:45PM  (435 to 885),    min meeting = 90 minutes.
# William:  at North Beach,         from 1:15PM to 8:15PM  (795 to 1215),   min meeting = 15 minutes.
# Daniel:   at Mission District,    from 7:00AM to 11:15AM (420 to 675),    min meeting = 105 minutes.
friends = [
    ("Golden Gate Park", 825, 900, 30),   # Jessica
    ("Bayview", 1035, 1200, 105),           # Ashley
    ("Chinatown", 435, 885, 90),            # Ronald
    ("North Beach", 795, 1215, 15),         # William
    ("Mission District", 420, 675, 105),    # Daniel
]
friend_names = ["Jessica", "Ashley", "Ronald", "William", "Daniel"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "Presidio"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]    : Bool - True if meeting with friend i is scheduled.
#   A[i]    : Int  - Arrival time at friend i's location (in minutes after midnight).
#   order[i]: Int  - The order in which friend i is visited if scheduled;
#                    if friend not scheduled, order[i] is fixed to -1.
x     = [Bool(f"x_{i}") for i in range(num_friends)]
A     = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then assign an order in [0, num_friends-1]; otherwise fix order to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that if two friends are both scheduled, they must have different order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend i that is scheduled, ensure the meeting fits within the available window.
# Meeting start time is the later of your arrival A[i] and the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # The meeting must end (meeting_start + duration) by avail_end.
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure travel time from starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings:
# If friend j is visited immediately after friend i then:
#   Arrival time at friend j must be at least the departure time from friend i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        # Meeting at i starts at max(A[i], avail_start_i) and lasts for 'dur_i'.
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time_ij))

# --------------------------------------------------------------------
# Objective: Maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            scheduled.append((model.evaluate(order[i]).as_long(), i))
    scheduled.sort()  # sort by order

    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    print("Optimal meeting schedule:")
    for ord_val, i in scheduled:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    total_meetings = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_meetings)
else:
    print("No feasible schedule found.")