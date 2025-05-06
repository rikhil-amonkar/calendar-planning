from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations used: Union Square, The Castro, North Beach, Embarcadero, Alamo Square,
# Nob Hill, Presidio, Fisherman's Wharf, Mission District, Haight-Ashbury.
travel = {
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Haight-Ashbury"): 18,

    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Haight-Ashbury"): 6,

    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Haight-Ashbury"): 18,

    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,

    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,

    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Haight-Ashbury"): 13,

    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Haight-Ashbury"): 15,

    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,

    ("Mission District", "Union Square"): 15,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,

    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined by a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# We start at Union Square at 9:00AM (540 minutes)
# Melissa: The Castro, 8:15PM (1215) - 9:15PM (1275), min 30 minutes.
# Kimberly: North Beach, 7:00AM (420) - 10:30AM (630), min 15 minutes.
# Joseph: Embarcadero, 3:30PM (930) - 7:30PM (1170), min 75 minutes.
# Barbara: Alamo Square, 8:45PM (1245) - 9:45PM (1305), min 15 minutes.
# Kenneth: Nob Hill, 12:15PM (735) - 5:15PM (1035), min 105 minutes.
# Joshua: Presidio, 4:30PM (990) - 6:15PM (1095), min 105 minutes.
# Brian: Fisherman's Wharf, 9:30AM (570) - 3:30PM (930), min 45 minutes.
# Steven: Mission District, 7:30PM (1170) - 9:00PM (1260), min 90 minutes.
# Betty: Haight-Ashbury, 7:00PM (1140) - 8:30PM (1230), min 90 minutes.
friends = [
    ("The Castro", 1215, 1275, 30),   # Melissa
    ("North Beach", 420, 630, 15),      # Kimberly
    ("Embarcadero", 930, 1170, 75),     # Joseph
    ("Alamo Square", 1245, 1305, 15),   # Barbara
    ("Nob Hill", 735, 1035, 105),       # Kenneth
    ("Presidio", 990, 1095, 105),       # Joshua
    ("Fisherman's Wharf", 570, 930, 45),# Brian
    ("Mission District", 1170, 1260, 90),# Steven
    ("Haight-Ashbury", 1140, 1230, 90), # Betty
]
friend_names = ["Melissa", "Kimberly", "Joseph", "Barbara", "Kenneth", "Joshua", "Brian", "Steven", "Betty"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Union Square"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] indicates whether a meeting with friend i is scheduled.
# A[i] is your arrival time (in minutes after midnight) at friend i's location.
# order[i] is the meeting order if scheduled (from 0 to num_friends-1; if not scheduled, it is fixed to -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then order[i] must be between 0 and num_friends-1, otherwise order[i] is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, enforce the meeting window constraints.
# The actual meeting start is the later of your arrival time and the friend's availability start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure there is enough travel time from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive scheduled meetings, if friend j is immediately after friend i, ensure travel time is respected.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings along with their order.
    scheduled = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            scheduled.append((model.evaluate(order[i]).as_long(), i))
    scheduled.sort()
    
    def to_time(t):
        h = t // 60
        m = t % 60
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