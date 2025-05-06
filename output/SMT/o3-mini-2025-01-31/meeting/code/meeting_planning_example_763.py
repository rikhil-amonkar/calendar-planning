from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    # From Chinatown
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    
    # From Embarcadero
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    
    # From Pacific Heights
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "The Castro"): 16,
    
    # From Russian Hill
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    
    # From Golden Gate Park
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    
    # From Fisherman's Wharf
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "The Castro"): 27,
    
    # From Sunset District
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "The Castro"): 17,
    
    # From The Castro
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Sunset District"): 17,
}

# ----------------------------------------------------------------------------
# Friend meeting data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration),
# where times are in minutes after midnight.
# You arrive at Chinatown at 9:00AM (540 minutes).
friends = [
    # 0: Richard at Embarcadero: 3:15PM to 6:45PM (915 to 1125), minimum meeting duration 90 minutes.
    ("Embarcadero", 915, 1125, 90),
    # 1: Mark at Pacific Heights: 3:00PM to 5:00PM (900 to 1020), minimum meeting duration 45 minutes.
    ("Pacific Heights", 900, 1020, 45),
    # 2: Matthew at Russian Hill: 5:30PM to 9:00PM (1050 to 1260), minimum meeting duration 90 minutes.
    ("Russian Hill", 1050, 1260, 90),
    # 3: Rebecca at Haight-Ashbury: 2:45PM to 6:00PM (885 to 1080), minimum meeting duration 60 minutes.
    ("Haight-Ashbury", 885, 1080, 60),
    # 4: Melissa at Golden Gate Park: 1:45PM to 5:30PM (825 to 1050), minimum meeting duration 90 minutes.
    ("Golden Gate Park", 825, 1050, 90),
    # 5: Margaret at Fisherman's Wharf: 2:45PM to 8:15PM (885 to 1155), minimum meeting duration 15 minutes.
    ("Fisherman's Wharf", 885, 1155, 15),
    # 6: Emily at Sunset District: 3:45PM to 5:00PM (945 to 1020), minimum meeting duration 45 minutes.
    ("Sunset District", 945, 1020, 45),
    # 7: George at The Castro: 2:00PM to 4:15PM (840 to 975), minimum meeting duration 75 minutes.
    ("The Castro", 840, 975, 75),
]
friend_names = ["Richard", "Mark", "Matthew", "Rebecca", "Melissa", "Margaret", "Emily", "George"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Chinatown"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] : Bool variable; True if meeting with friend i is scheduled.
# A[i] : Int variable for arrival time at friend i's location.
# order[i] : Int variable that represents the order in which friend i is visited (if scheduled).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled, assign order in the range [0, num_friends-1];
# otherwise fix the order to -1. Also enforce A[i] >= 0.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For each scheduled meeting, the meeting start time is the later of your arrival A[i]
# and the friend’s available start. The meeting must finish (start time + duration) by the friend’s available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location.
# For any meeting that is first in the order (order[i] == 0), the arrival time must be no earlier than:
# start_time + travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# If meeting j immediately follows meeting i (order[j] == order[i] + 1),
# then your arrival at meeting j must be at least the departure time from meeting i (meeting start + duration)
# plus the travel time from friend i's location to friend j's location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        loc_j, _, _, _ = friends[j]
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()

    def to_time(t):
        hrs = t // 60
        mins = t % 60
        return f"{hrs:02d}:{mins:02d}"

    print("Optimal meeting schedule:")
    # Collect scheduled meetings and their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    for ord_val, i in schedule:
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