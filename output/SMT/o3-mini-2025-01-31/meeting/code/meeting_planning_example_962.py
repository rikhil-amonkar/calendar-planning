from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Each key is a tuple: (From, To)
travel = {
    # From The Castro
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Sunset District"): 17,
    
    # From Marina District
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Sunset District"): 19,
    
    # From Presidio
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    
    # From North Beach
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    
    # From Embarcadero
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Sunset District"): 30,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Sunset District"): 15,
    
    # From Golden Gate Park
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Sunset District"): 10,
    
    # From Richmond District
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Sunset District"): 11,
    
    # From Alamo Square
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Sunset District"): 16,
    
    # From Financial District
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Sunset District"): 30,
    
    # From Sunset District
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
}

# --------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration)
#
# Times are in minutes after midnight.
# Elizabeth: at Marina District from 7:00PM to 8:45PM,   min meeting = 105 minutes.
# Joshua:    at Presidio         from 8:30AM to 1:15PM,   min meeting = 105 minutes.
# Timothy:   at North Beach      from 7:45PM to 10:00PM,  min meeting = 90 minutes.
# David:     at Embarcadero      from 10:45AM to 12:30PM, min meeting = 30 minutes.
# Kimberly:  at Haight-Ashbury   from 4:45PM to 9:30PM,   min meeting = 75 minutes.
# Lisa:      at Golden Gate Park  from 5:30PM to 9:45PM,   min meeting = 45 minutes.
# Ronald:    at Richmond District from 8:00AM to 9:30AM,   min meeting = 90 minutes.
# Stephanie: at Alamo Square    from 3:30PM to 4:30PM,   min meeting = 30 minutes.
# Helen:     at Financial District from 5:30PM to 6:30PM,   min meeting = 45 minutes.
# Laura:     at Sunset District   from 5:45PM to 9:15PM,   min meeting = 90 minutes.
friends = [
    ("Marina District",   1140, 1245, 105),  # Elizabeth
    ("Presidio",           510,  795, 105),  # Joshua
    ("North Beach",       1185, 1320, 90),   # Timothy
    ("Embarcadero",        645,  750, 30),    # David
    ("Haight-Ashbury",    1005, 1290, 75),   # Kimberly
    ("Golden Gate Park",  1050, 1305, 45),   # Lisa
    ("Richmond District",  480,  570, 90),   # Ronald
    ("Alamo Square",       930,  990, 30),   # Stephanie
    ("Financial District", 1050, 1110, 45),   # Helen
    ("Sunset District",    1065, 1275, 90),   # Laura
]
friend_names = ["Elizabeth", "Joshua", "Timothy", "David", "Kimberly", "Lisa", "Ronald", "Stephanie", "Helen", "Laura"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "The Castro"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]    : Bool, True if meeting with friend i is scheduled.
#   A[i]    : Int, arrival time (in minutes after midnight) at friend i's location.
#   order[i]: Int, index in which friend i is visited if scheduled; if not, fixed to -1.
x     = [Bool(f"x_{i}") for i in range(num_friends)]
A     = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then order in [0, num_friends-1] is assigned; otherwise, fix order = -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend i that is scheduled, ensure the meeting fits within the available window.
# The meeting starts at the later between your arrival A[i] and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), you must travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings: if friend j immediately follows friend i then your arrival at j must be at least
# the departure time (meeting start + duration) from i plus travel time from i's location to j's location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        t_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + t_time))

# --------------------------------------------------------------------
# Objective: Maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the optimal meeting schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by order index

    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        start_meet = arrival if arrival >= avail_start else avail_start
        end_meet = start_meet + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(start_meet)} to {to_time(end_meet)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")