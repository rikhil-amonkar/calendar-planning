from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    # From Sunset District
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Alamo Square"): 17,
    
    # From Presidio
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    
    # From Nob Hill
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    
    # From Pacific Heights
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Alamo Square"): 10,
    
    # From Mission District
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    
    # From Marina District
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Alamo Square"): 15,
    
    # From North Beach
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    
    # From Russian Hill
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Alamo Square"): 15,
    
    # From Richmond District
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Alamo Square"): 13,
    
    # From Embarcadero
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    
    # From Alamo Square
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Embarcadero"): 16,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# All times are in minutes after midnight.
# You arrive at Sunset District at 9:00AM (540 minutes).
friends = [
    # 0: Charles at Presidio: 1:15PM to 3:00PM (795 to 900), minimum meeting duration 105 minutes.
    ("Presidio", 795, 900, 105),
    # 1: Robert at Nob Hill: 1:15PM to 5:30PM (795 to 1050), minimum meeting duration 90 minutes.
    ("Nob Hill", 795, 1050, 90),
    # 2: Nancy at Pacific Heights: 2:45PM to 10:00PM (885 to 1320), minimum meeting duration 105 minutes.
    ("Pacific Heights", 885, 1320, 105),
    # 3: Brian at Mission District: 3:30PM to 10:00PM (930 to 1320), minimum meeting duration 60 minutes.
    ("Mission District", 930, 1320, 60),
    # 4: Kimberly at Marina District: 5:00PM to 7:45PM (1020 to 1185), minimum meeting duration 75 minutes.
    ("Marina District", 1020, 1185, 75),
    # 5: David at North Beach: 2:45PM to 4:30PM (885 to 990), minimum meeting duration 75 minutes.
    ("North Beach", 885, 990, 75),
    # 6: William at Russian Hill: 12:30PM to 7:15PM (750 to 1155), minimum meeting duration 120 minutes.
    ("Russian Hill", 750, 1155, 120),
    # 7: Jeffrey at Richmond District: 12:00PM to 7:15PM (720 to 1155), minimum meeting duration 45 minutes.
    ("Richmond District", 720, 1155, 45),
    # 8: Karen at Embarcadero: 2:15PM to 8:45PM (855 to 1245), minimum meeting duration 60 minutes.
    ("Embarcadero", 855, 1245, 60),
    # 9: Joshua at Alamo Square: 6:45PM to 10:00PM (1125 to 1320), minimum meeting duration 60 minutes.
    ("Alamo Square", 1125, 1320, 60),
]
friend_names = ["Charles", "Robert", "Nancy", "Brian", "Kimberly", "David", "William", "Jeffrey", "Karen", "Joshua"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Sunset District"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Bool, True if meeting friend i is scheduled.
# A[i]: Int, arrival time at friend i's location.
# order[i]: Int, the order in which friend i is visited (if scheduled).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled, order[i] is in [0, num_friends-1] (otherwise fixed to -1), and arrival time is nonnegative.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i + 1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For each friend meeting, the meeting start is the later of your arrival A[i] and the friend's avail_start.
# The meeting must last at least the minimum duration and finish by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the start location.
# For any scheduled meeting that is first (order[i] == 0), you must account for travel from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# If meeting j immediately follows meeting i (order[j] == order[i] + 1), then your arrival time at j
# must be at least the departure time from meeting i (meeting_start + min_duration) plus travel time.
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
# Objective: maximize the number of meetings scheduled.
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
    # Collect scheduled meetings with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting starts at the later of arrival and the available start time.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")