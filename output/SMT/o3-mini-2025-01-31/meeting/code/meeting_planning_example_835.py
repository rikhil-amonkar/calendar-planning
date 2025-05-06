from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ---------------------------------------------------------------------
# Travel time (in minutes) between locations (directional).
# Only the distances given in the problem are included.
travel = {
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Mission District"): 15,
    
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Mission District"): 17,
    
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Mission District"): 7,
    
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Mission District"): 13,
    
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Mission District"): 20,
    
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Mission District"): 14,
    
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Mission District"): 25,
    
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
}

# ---------------------------------------------------------------------
# Friend meeting details.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
#
# You arrive at Pacific Heights at 9:00AM = 540 minutes.
#
# Friends:
#   Helen     : Golden Gate Park   from 9:30AM (570)  to 12:15PM (735); meeting >= 45 minutes.
#   Steven    : The Castro         from 8:15PM (1215) to 10:00PM (1320); meeting >= 105 minutes.
#   Deborah   : Bayview            from 8:30AM (510)  to 12:00PM (720); meeting >= 30 minutes.
#   Matthew   : Marina District    from 9:15AM (555)  to 2:15PM (855); meeting >= 45 minutes.
#   Joseph    : Union Square       from 2:15PM (855)  to 6:45PM (1125); meeting >= 120 minutes.
#   Ronald    : Sunset District    from 4:00PM (960)  to 8:45PM (1245); meeting >= 60 minutes.
#   Robert    : Alamo Square       from 6:30PM (1110) to 9:15PM (1275); meeting >= 120 minutes.
#   Rebecca   : Financial District from 2:45PM (885)  to 4:15PM (975); meeting >= 30 minutes.
#   Elizabeth : Mission District   from 6:30PM (1110) to 9:00PM (1260); meeting >= 120 minutes.
friends = [
    ("Golden Gate Park", 570, 735, 45),    # Helen
    ("The Castro", 1215, 1320, 105),         # Steven
    ("Bayview", 510, 720, 30),               # Deborah
    ("Marina District", 555, 855, 45),       # Matthew
    ("Union Square", 855, 1125, 120),         # Joseph
    ("Sunset District", 960, 1245, 60),       # Ronald
    ("Alamo Square", 1110, 1275, 120),        # Robert
    ("Financial District", 885, 975, 30),      # Rebecca
    ("Mission District", 1110, 1260, 120)      # Elizabeth
]
friend_names = ["Helen", "Steven", "Deborah", "Matthew", "Joseph", "Ronald", "Robert", "Rebecca", "Elizabeth"]
num_friends = len(friends)

# Starting location and time.
start_loc = "Pacific Heights"
start_time = 540  # 9:00AM

# ---------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# For each friend i:
#   x[i]    : Bool, True if friend i meeting is scheduled.
#   A[i]    : Int, the arrival time (minutes after midnight) at friend i's location.
#   order[i]: Int, the order (if scheduled; if not, fixed to -1) in the itinerary.
x      = [Bool(f"x_{i}") for i in range(num_friends)]
A      = [Int(f"A_{i}") for i in range(num_friends)]
order  = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled, order is between 0 and num_friends-1.
# Otherwise, order[i] is set to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting time-window constraints.
# For each friend i, if scheduled, the meeting starts at max(A[i], avail_start)
# and must end (start + duration) no later than avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# For the first scheduled meeting (order == 0), you travel from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    # There must be enough time from the start time plus travel from start_loc.
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings: If friend j follows friend i immediately (order[j]==order[i]+1),
# then the arrival time at j must be at least the departure time from i plus travel time between i and j.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j: continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time))

# Objective: Maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    def to_time(minutes):
        hr = minutes // 60
        mn = minutes % 60
        return f"{hr:02d}:{mn:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting starts when you arrive or when the friend becomes available (whichever is later)
        start_meet = arrival if arrival >= avail_start else avail_start
        end_meet = start_meet + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(start_meet)} to {to_time(end_meet)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")