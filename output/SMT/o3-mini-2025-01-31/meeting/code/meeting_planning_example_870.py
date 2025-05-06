from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Pacific Heights, Marina District, The Castro, Richmond District, 
# Alamo Square, Financial District, Presidio, Mission District, Nob Hill, Russian Hill.
travel = {
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,
    
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,
    
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,
    
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Nob Hill"): 5,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple:
#   (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Starting point: Pacific Heights at 9:00AM (540 minutes)
friends = [
    # Linda at Marina District: 6:00PM (1080) to 10:00PM (1320), min 30.
    ("Marina District", 1080, 1320, 30),
    # Kenneth at The Castro: 2:45PM (885) to 4:15PM (975), min 30.
    ("The Castro", 885, 975, 30),
    # Kimberly at Richmond District: 2:15PM (855) to 10:00PM (1320), min 30.
    ("Richmond District", 855, 1320, 30),
    # Paul at Alamo Square: 9:00PM (1260) to 9:30PM (1290), min 15.
    ("Alamo Square", 1260, 1290, 15),
    # Carol at Financial District: 10:15AM (615) to 12:00PM (720), min 60.
    ("Financial District", 615, 720, 60),
    # Brian at Presidio: 10:00AM (600) to 9:30PM (1290), min 75.
    ("Presidio", 600, 1290, 75),
    # Laura at Mission District: 4:15PM (975) to 8:30PM (1230), min 30.
    ("Mission District", 975, 1230, 30),
    # Sandra at Nob Hill: 9:15AM (555) to 6:30PM (1110), min 60.
    ("Nob Hill", 555, 1110, 60),
    # Karen at Russian Hill: 6:30PM (1110) to 10:00PM (1320), min 75.
    ("Russian Hill", 1110, 1320, 75),
]
friend_names = ["Linda", "Kenneth", "Kimberly", "Paul", "Carol",
                "Brian", "Laura", "Sandra", "Karen"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Pacific Heights"
start_time = 540  # 9:00 AM in minutes after midnight

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean indicating whether meeting friend i is scheduled.
# A[i]: Integer representing arrival time (in minutes after midnight) at friend i's location.
# order[i]: Integer representing the sequence order of the meeting (if scheduled, in 0..num_friends-1; otherwise, -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled then order[i] is in valid range; if not, it is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    # Ensure arrival times are non-negative.
    opt.add(A[i] >= 0)

# No two scheduled meetings should share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting time constraints:
# The meeting starts at the later of your arrival time A[i] and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, min_duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # If meeting scheduled then meeting must finish within available window.
    opt.add(Or(Not(x[i]), meeting_start + min_duration <= avail_end))

# Travel constraint for the first scheduled meeting from the starting point.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# Travel constraints between consecutive scheduled meetings.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, duration_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + duration_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        # If meeting j follows meeting i, enforce travel time.
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect and sort scheduled meetings by order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    def to_time(t):
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, duration = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + duration
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    
    total_meetings = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_meetings)
else:
    print("No feasible schedule found.")