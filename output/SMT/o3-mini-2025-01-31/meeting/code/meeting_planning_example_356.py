from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Union Square"): 17,
    
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    
    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Union Square"): 22,
    
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 17,
    
    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18
}

# Define friend meeting details.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Barbara: at North Beach from 1:45PM (825) to 8:15PM (1215) with a minimum meeting of 60 minutes.
    ("North Beach", 825, 1215, 60),
    # Margaret: at Presidio from 10:15AM (615) to 3:15PM (915) with a minimum meeting of 30 minutes.
    ("Presidio", 615, 915, 30),
    # Kevin: at Haight-Ashbury from 8:00PM (1200) to 8:45PM (1245) with a minimum meeting of 30 minutes.
    ("Haight-Ashbury", 1200, 1245, 30),
    # Kimberly: at Union Square from 7:45AM (465) to 4:45PM (1005) with a minimum meeting of 30 minutes.
    ("Union Square", 465, 1005, 30)
]
friend_names = ["Barbara", "Margaret", "Kevin", "Kimberly"]
num_friends = len(friends)

# Starting conditions:
# You arrive at Bayview at 9:00AM (540 minutes after midnight).
start_loc = "Bayview"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
# For each friend i:
#   x[i]    : Bool that indicates whether the meeting is scheduled.
#   A[i]    : Integer for your arrival time at friend i's location.
#   order[i]: Integer indicating the position of the meeting in the itinerary.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constrain order variable:
# If a meeting is scheduled then order[i] is in [0, num_friends-1], else order[i] == -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that all scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# For each friend, if meeting i is scheduled then the effective meeting start time is
# the later of your arrival time A[i] and the friend’s available start.
# The meeting must finish (meeting start + min_duration) by the friend's available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints for the first meeting:
# For any friend i that is scheduled as the first meeting (order==0),
# your arrival time A[i] must be no less than (start_time + travel time from start_loc to friend i).
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings:
# If meeting j immediately follows meeting i (order[j] == order[i] + 1),
# then arrival A[j] must be at least the departure time from meeting i plus the travel time.
# Departure time from meeting i is defined as max(A[i], avail_start_i) + min_duration_i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_start_i, avail_start_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + t_time))

# Objective: Maximize the total number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization problem and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Helper to format minutes after midnight as HH:MM.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")