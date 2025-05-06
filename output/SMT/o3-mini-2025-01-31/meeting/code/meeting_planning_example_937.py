from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Presidio"): 16,
    
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,
    
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Presidio"): 7,
    
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Presidio"): 20,
    
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Presidio"): 20,
    
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Presidio"): 17,
    
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Alamo Square"): 19,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are expressed in minutes after midnight. You start at Russian Hill at 9:00AM (540 minutes).
friends = [
    # 0: David at Sunset District: 9:15AM to 10:00PM (555 to 1320), min 15 minutes.
    ("Sunset District", 555, 1320, 15),
    # 1: Kenneth at Union Square: 9:15PM to 9:45PM (1275 to 1305), min 15 minutes.
    ("Union Square", 1275, 1305, 15),
    # 2: Patricia at Nob Hill: 3:00PM to 7:15PM (900 to 1155), min 120 minutes.
    ("Nob Hill", 900, 1155, 120),
    # 3: Mary at Marina District: 2:45PM to 4:45PM (885 to 1005), min 45 minutes.
    ("Marina District", 885, 1005, 45),
    # 4: Charles at Richmond District: 5:15PM to 9:00PM (1035 to 1260), min 15 minutes.
    ("Richmond District", 1035, 1260, 15),
    # 5: Joshua at Financial District: 2:30PM to 5:15PM (870 to 1035), min 90 minutes.
    ("Financial District", 870, 1035, 90),
    # 6: Ronald at Embarcadero: 6:15PM to 8:45PM (1095 to 1245), min 30 minutes.
    ("Embarcadero", 1095, 1245, 30),
    # 7: George at The Castro: 2:15PM to 7:00PM (855 to 1140), min 105 minutes.
    ("The Castro", 855, 1140, 105),
    # 8: Kimberly at Alamo Square: 9:00AM to 2:30PM (540 to 870), min 105 minutes.
    ("Alamo Square", 540, 870, 105),
    # 9: William at Presidio: 7:00AM to 12:45PM (420 to 765), min 60 minutes.
    ("Presidio", 420, 765, 60),
]
friend_names = ["David", "Kenneth", "Patricia", "Mary", "Charles", "Joshua", "Ronald", "George", "Kimberly", "William"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Russian Hill"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] is a Boolean: True if meeting friend i is scheduled.
# A[i] is the arrival time at friend i's location.
# order[i] is the sequence order for meeting friend i (0 .. num_friends-1 if scheduled, else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If scheduled, order[i] should be between 0 and num_friends - 1;
# otherwise, we set order[i] to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints:
# For each scheduled meeting, the meeting starts at the later of your arrival time A[i]
# and the friend’s available start; then the meeting lasts at least the specified duration.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location for the first meeting.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    # If friend i is the first meeting (order[i]==0) then A[i] must be at least start_time + travel_time.
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# If friend j is visited immediately after friend i then:
#   A[j] must be at least (max(A[i], avail_start_i) + min_duration_i + travel_time from i to j)
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    # Collect scheduled meetings and sort them by order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    def to_time(t):
        hrs = t // 60
        mins = t % 60
        return f"{hrs:02d}:{mins:02d}"
    
    print("Optimal meeting schedule:")
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