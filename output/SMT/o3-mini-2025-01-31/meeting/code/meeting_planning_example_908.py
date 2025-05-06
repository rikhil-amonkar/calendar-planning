from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between neighborhoods.
# Locations: Financial District, Fisherman's Wharf, Presidio, Bayview,
# Haight-Ashbury, Russian Hill, The Castro, Marina District, Richmond District,
# Union Square, Sunset District.
travel = {
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,
    
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,
    
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Union Square"): 30,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# Times are expressed in minutes after midnight.
#
# Mark:       at Fisherman's Wharf from 8:15AM to 10:00AM  => [495, 600], min_duration=30.
# Stephanie:  at Presidio from 12:15PM to 3:00PM         => [735, 900], min_duration=75.
# Betty:      at Bayview from 7:15AM to 8:30PM            => [435, 1230], min_duration=15.
# Lisa:       at Haight-Ashbury from 3:30PM to 6:30PM      => [930, 1110], min_duration=45.
# William:    at Russian Hill from 6:45PM to 8:00PM         => [1125, 1200], min_duration=60.
# Brian:      at The Castro from 9:15AM to 1:15PM           => [555, 795], min_duration=30.
# Joseph:     at Marina District from 10:45AM to 3:00PM     => [645, 900], min_duration=90.
# Ashley:     at Richmond District from 9:45AM to 11:15AM   => [585, 675], min_duration=45.
# Patricia:   at Union Square from 4:30PM to 8:00PM         => [990, 1200], min_duration=120.
# Karen:      at Sunset District from 4:30PM to 10:00PM       => [990, 1320], min_duration=105.
friends = [
    ("Fisherman's Wharf", 495, 600, 30),    # Mark
    ("Presidio",            735, 900, 75),    # Stephanie
    ("Bayview",             435, 1230, 15),   # Betty
    ("Haight-Ashbury",      930, 1110, 45),   # Lisa
    ("Russian Hill",       1125, 1200, 60),   # William
    ("The Castro",         555, 795, 30),     # Brian
    ("Marina District",     645, 900, 90),    # Joseph
    ("Richmond District",   585, 675, 45),    # Ashley
    ("Union Square",        990, 1200, 120),  # Patricia
    ("Sunset District",       990, 1320, 105), # Karen
]
friend_names = ["Mark", "Stephanie", "Betty", "Lisa", "William", "Brian", "Joseph", "Ashley", "Patricia", "Karen"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Financial District"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
#   x[i] : Boolean flag indicating whether meeting with friend i is scheduled.
#   A[i] : Integer arrival time at friend i's location (in minutes).
#   order[i] : Integer representing the visitation order for friend i if scheduled, else -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled then its order is in range [0, num_friends-1], otherwise set to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that any two scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled, the meeting starts at the later of your arrival and the friend’s available start.
# Meeting must finish (start time + min_duration) no later than the friend’s available end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure you have enough travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j follows friend i then travel time must be observed.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + friends[i][3]  # meeting duration for i
        travel_time_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather and sort scheduled meetings by visitation order.
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
        arr_time = model.evaluate(A[i]).as_long()
        start_meeting = arr_time if arr_time >= avail_start else avail_start
        end_meeting = start_meeting + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arr_time)}")
        print(f"    Meeting Time: {to_time(start_meeting)} - {to_time(end_meeting)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")