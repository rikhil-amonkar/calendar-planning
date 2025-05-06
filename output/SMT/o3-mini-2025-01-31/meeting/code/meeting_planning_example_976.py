from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# The keys are (origin, destination)
travel = {
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,

    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,

    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Marina District"): 12,

    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,

    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,

    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,

    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,

    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,

    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,

    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Marina District"): 9,

    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Fisherman's Wharf"): 10,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is a tuple in the form:
#   (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You arrive at Embarcadero at 9:00AM (540 minutes).
friends = [
    # 0: Matthew at Bayview: 7:15PM to 10:00PM (1155 to 1320), min 120 min.
    ("Bayview", 1155, 1320, 120),
    # 1: Karen at Chinatown: 7:15PM to 9:15PM (1155 to 1275), min 90 min.
    ("Chinatown", 1155, 1275, 90),
    # 2: Sarah at Alamo Square: 8:00PM to 9:45PM (1200 to 1305), min 105 min.
    ("Alamo Square", 1200, 1305, 105),
    # 3: Jessica at Nob Hill: 4:30PM to 6:45PM (990 to 1125), min 120 min.
    ("Nob Hill", 990, 1125, 120),
    # 4: Stephanie at Presidio: 7:30AM to 10:15AM (450 to 615), min 60 min.
    ("Presidio", 450, 615, 60),
    # 5: Mary at Union Square: 4:45PM to 9:30PM (1005 to 1290), min 60 min.
    ("Union Square", 1005, 1290, 60),
    # 6: Charles at The Castro: 4:30PM to 10:00PM (990 to 1320), min 105 min.
    ("The Castro", 990, 1320, 105),
    # 7: Nancy at North Beach: 2:45PM to 8:00PM (885 to 1200), min 15 min.
    ("North Beach", 885, 1200, 15),
    # 8: Thomas at Fisherman's Wharf: 1:30PM to 7:00PM (810 to 1140), min 30 min.
    ("Fisherman's Wharf", 810, 1140, 30),
    # 9: Brian at Marina District: 12:15PM to 6:00PM (735 to 1080), min 60 min.
    ("Marina District", 735, 1080, 60),
]
friend_names = ["Matthew", "Karen", "Sarah", "Jessica", "Stephanie",
                "Mary", "Charles", "Nancy", "Thomas", "Brian"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Embarcadero"
start_time = 540  # 9:00 AM in minutes after midnight

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] is a Boolean that indicates if you schedule a meeting with friend i.
# A[i] is the arrival time (in minutes after midnight) for friend i.
# order[i] is the order in which friend i is visited (if scheduled, range 0..num_friends-1, otherwise -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If meeting is scheduled then order is between 0 and num_friends-1; otherwise, order is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# No two scheduled meetings should share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints:
# The meeting starts at the later of your arrival time and the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # If meeting is scheduled then it must finish (meeting_start + min_dur) by avail_end.
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location (Embarcadero) for the first scheduled meeting.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
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
    # Collect scheduled meetings along with their order.
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
        # Meeting starts at the later of arrival and available start time.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")