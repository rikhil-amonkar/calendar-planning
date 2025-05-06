from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Locations: Golden Gate Park, Alamo Square, Presidio, Russian Hill.
# Provided travel times:
# Golden Gate Park to Alamo Square: 10.
# Golden Gate Park to Presidio: 11.
# Golden Gate Park to Russian Hill: 19.
# Alamo Square to Golden Gate Park: 9.
# Alamo Square to Presidio: 18.
# Alamo Square to Russian Hill: 13.
# Presidio to Golden Gate Park: 12.
# Presidio to Alamo Square: 18.
# Presidio to Russian Hill: 14.
# Russian Hill to Golden Gate Park: 21.
# Russian Hill to Alamo Square: 15.
# Russian Hill to Presidio: 14.
travel = {
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Russian Hill"): 13,
    
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Starting at Golden Gate Park at 9:00AM (540 minutes).
#
# Timothy: at Alamo Square from 12:00PM to 4:15PM => [720, 975], min_duration = 105.
# Mark: at Presidio from 6:45PM to 9:00PM      => [1125, 1260], min_duration = 60.
# Joseph: at Russian Hill from 4:45PM to 9:30PM  => [16:45?] Actually 4:45PM = 16*60+45 = 1005, and end at 9:30PM = 1290; min_duration = 60.
friends = [
    ("Alamo Square", 720, 975, 105),   # Timothy
    ("Presidio",     1125, 1260, 60),    # Mark
    ("Russian Hill", 1005, 1290, 60),    # Joseph
]
friend_names = ["Timothy", "Mark", "Joseph"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Start parameters.
start_loc = "Golden Gate Park"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] : Bool variable indicating if friend i is scheduled
# A[i] : Int variable for arrival time at friend i's location.
# order[i] : Int variable for the visitation order if friend i is met (if not met, order=-1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled, then order is between 0 and num_friends-1;
# otherwise, enforce order[i] == -1. Also ensure arrival time is nonnegative.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Ensure that any two scheduled meetings have different order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, force the meeting to end within its available window.
# The meeting starts at the later of arrival time and its available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# Constraint: For the first scheduled meeting (order == 0), ensure enough travel time from starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# Constraint: For consecutive meetings, if friend j follows friend i then travel time must be observed.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and print out the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Get scheduled meetings and sort them by order.
    scheduled = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            scheduled.append((model.evaluate(order[i]).as_long(), i))
    scheduled.sort()
    
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
        
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")