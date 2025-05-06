from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define travel distances (in minutes, directional) between locations.
travel = {
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Embarcadero"): 14,
    
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Embarcadero"): 19,
    
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Embarcadero"): 30,
    
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Embarcadero"): 19,
    
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Embarcadero"): 9,
    
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Embarcadero"): 5,
    
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Embarcadero"): 6,
    
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Russian Hill"): 8
}

# Define friend meeting information.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Charles at Bayview: available 11:30AM to 2:30PM (690 to 870), meeting at least 45 minutes.
    ("Bayview", 690, 870, 45),
    # Robert at Sunset District: available 4:45PM to 9:00PM (1005 to 1260), meeting at least 30 minutes.
    ("Sunset District", 1005, 1260, 30),
    # Karen at Richmond District: available 7:15PM to 9:30PM (1155 to 1290), meeting at least 60 minutes.
    ("Richmond District", 1155, 1290, 60),
    # Rebecca at Nob Hill: available 4:15PM to 8:30PM (975 to 1230), meeting at least 90 minutes.
    ("Nob Hill", 975, 1230, 90),
    # Margaret at Chinatown: available 2:15PM to 7:45PM (855 to 1185), meeting at least 120 minutes.
    ("Chinatown", 855, 1185, 120),
    # Patricia at Haight-Ashbury: available 2:30PM to 8:30PM (870 to 1230), meeting at least 45 minutes.
    ("Haight-Ashbury", 870, 1230, 45),
    # Mark at North Beach: available 2:00PM to 6:30PM (840 to 1110), meeting at least 105 minutes.
    ("North Beach", 840, 1110, 105),
    # Melissa at Russian Hill: available 1:00PM to 7:45PM (780 to 1185), meeting at least 30 minutes.
    ("Russian Hill", 780, 1185, 30),
    # Laura at Embarcadero: available 7:45AM to 1:15PM (465 to 795), meeting at least 105 minutes.
    ("Embarcadero", 465, 795, 105)
]
num_friends = len(friends)

# Starting conditions:
# You arrive at Marina District at 9:00AM = 540 minutes after midnight.
start_loc = "Marina District"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i define decision variables:
#  x[i]  : Bool. True if you schedule a meeting with friend i.
#  A[i]  : Arrival time (minutes after midnight) at friend i's location.
#  order[i] : The position of friend i in your schedule (0..num_friends-1) if scheduled; -1 otherwise.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

for i in range(num_friends):
    # If scheduled then order is between 0 and num_friends-1,
    # otherwise order must be -1.
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraint:
# For friend i with availability [avail_start, avail_end] and minimum meeting duration min_dur,
# the meeting will start at max(A[i], avail_start). This meeting must finish by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), you travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings:
# If friend j immediately follows friend i (i.e. order[j] == order[i] + 1),
# then arrival time at j must be at least the departure from i plus the travel time.
# Departure time from friend i = max(A[i], avail_start_i) + min_dur_i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + t_time))

# The objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and print the resulting schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings and sort them by order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Helper function to convert minutes after midnight to HH:MM.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Charles", "Robert", "Karen", "Rebecca", "Margaret",
                    "Patricia", "Mark", "Melissa", "Laura"]
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The meeting starts at the later of your arrival time and the friend’s available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")