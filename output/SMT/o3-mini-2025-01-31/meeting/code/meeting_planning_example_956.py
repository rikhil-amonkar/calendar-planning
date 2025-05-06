from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
# Only the travel times provided in the problem are included.
travel = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Pacific Heights"): 16,
}

# Define the friend meeting details.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You arrive at The Castro at 9:00AM which is 540 minutes.
friends = [
    # William: at Alamo Square from 3:15PM (915) to 5:15PM (1035); meeting >= 60 minutes.
    ("Alamo Square", 915, 1035, 60),
    # Joshua: at Richmond District from 7:00AM (420) to 8:00PM (1200); meeting >= 15 minutes.
    ("Richmond District", 420, 1200, 15),
    # Joseph: at Financial District from 11:15AM (675) to 1:30PM (810); meeting >= 15 minutes.
    ("Financial District", 675, 810, 15),
    # David: at Union Square from 4:45PM (1005) to 7:15PM (1155); meeting >= 45 minutes.
    ("Union Square", 1005, 1155, 45),
    # Brian: at Fisherman's Wharf from 1:45PM (825) to 8:45PM (1245); meeting >= 105 minutes.
    ("Fisherman's Wharf", 825, 1245, 105),
    # Karen: at Marina District from 11:30AM (690) to 6:30PM (1110); meeting >= 15 minutes.
    ("Marina District", 690, 1110, 15),
    # Anthony: at Haight-Ashbury from 7:15AM (435) to 10:30AM (630); meeting >= 30 minutes.
    ("Haight-Ashbury", 435, 630, 30),
    # Matthew: at Mission District from 5:15PM (1035) to 7:15PM (1155); meeting >= 120 minutes.
    ("Mission District", 1035, 1155, 120),
    # Helen: at Pacific Heights from 8:00AM (480) to 12:00PM (720); meeting >= 75 minutes.
    ("Pacific Heights", 480, 720, 75),
    # Jeffrey: at Golden Gate Park from 7:00PM (1140) to 9:30PM (1290); meeting >= 60 minutes.
    ("Golden Gate Park", 1140, 1290, 60)
]
friend_names = ["William", "Joshua", "Joseph", "David", "Brian", "Karen", "Anthony", "Matthew", "Helen", "Jeffrey"]
num_friends = len(friends)

# Starting location and time.
start_loc = "The Castro"
start_time = 540  # 9:00AM

# Create the Z3 optimizer.
opt = Optimize()

# Decision variables for each friend:
# x[i]: Bool, whether the meeting is scheduled.
# A[i]: Int, the arrival time (in minutes) at friend i's location.
# order[i]: Int, the position in the itinerary (if scheduled, between 0 and num_friends-1; otherwise -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constraint: if a meeting is scheduled then order is in [0, num_friends-1]; otherwise, it is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure all scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting time-window constraints:
# For each friend, if scheduled, the actual meeting starts at max(A[i], avail_start)
# and must finish (start + min_duration) no later than avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For any scheduled meeting with order 0, your arrival time must be at least start_time + travel time
# from the starting location (The Castro) to the friend’s location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# Travel constraints for consecutive meetings:
# If meeting j immediately follows meeting i (order[j] == order[i] + 1), then your arrival time at j
# must be at least the departure time from meeting i plus travel time from i's location to j's location.
# The departure time from meeting i is calculated as max(A[i], avail_start_i) + min_duration_i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization problem and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings along with their order positions.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting starts at the later of arrival time and the available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")