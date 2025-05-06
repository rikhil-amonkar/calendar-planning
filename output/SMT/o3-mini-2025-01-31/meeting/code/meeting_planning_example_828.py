from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) among locations.
# Locations: Marina District, Richmond District, Union Square, Nob Hill,
# Fisherman's Wharf, Golden Gate Park, Embarcadero, Financial District, North Beach, Presidio.
travel = {
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Presidio"): 10,

    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Presidio"): 7,

    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,

    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Presidio"): 17,

    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Presidio"): 17,

    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Presidio"): 11,

    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,

    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Presidio"): 22,

    ("North Beach", "Marina District"): 9,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Presidio"): 17,

    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Stephanie at Richmond District: 4:15PM (975) - 9:30PM (1290), min 75 minutes.
    ("Richmond District", 975, 1290, 75),
    # William at Union Square: 10:45AM (645) - 5:30PM (1050), min 45 minutes.
    ("Union Square", 645, 1050, 45),
    # Elizabeth at Nob Hill: 12:15PM (735) - 3:00PM (900), min 105 minutes.
    ("Nob Hill", 735, 900, 105),
    # Joseph at Fisherman's Wharf: 12:45PM (765) - 2:00PM (840), min 75 minutes.
    ("Fisherman's Wharf", 765, 840, 75),
    # Anthony at Golden Gate Park: 1:00PM (780) - 8:30PM (1230), min 75 minutes.
    ("Golden Gate Park", 780, 1230, 75),
    # Barbara at Embarcadero: 7:15PM (1155) - 8:30PM (1230), min 75 minutes.
    ("Embarcadero", 1155, 1230, 75),
    # Carol at Financial District: 11:45AM (705) - 4:15PM (975), min 60 minutes.
    ("Financial District", 705, 975, 60),
    # Sandra at North Beach: 10:00AM (600) - 12:30PM (750), min 15 minutes.
    ("North Beach", 600, 750, 15),
    # Kenneth at Presidio: 9:15PM (1275) - 10:15PM (1335), min 45 minutes.
    ("Presidio", 1275, 1335, 45),
]
friend_names = ["Stephanie", "William", "Elizabeth", "Joseph", "Anthony", "Barbara", "Carol", "Sandra", "Kenneth"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
# You arrive at Marina District at 9:00AM (540 minutes after midnight)
start_loc = "Marina District"
start_time = 540

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]    : Boolean indicating whether meeting with friend i is scheduled.
# A[i]    : Arrival time at friend i's location (in minutes after midnight).
# order[i]: Order of the meeting (if scheduled then an integer between 0 and num_friends-1, else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then order[i] must be between 0 and num_friends-1,
# otherwise order[i] == -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure distinct order numbers for scheduled meetings.
for i in range(num_friends):
    for j in range(i + 1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled friend, enforce that the meeting fits within the friend’s available window.
# The meeting starts at the later of your arrival A[i] or the friend’s availability start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure you have enough travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive scheduled meetings: if friend j is visited immediately after friend i, ensure travel time is respected.
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
# Objective: maximize the number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival_time = model.evaluate(A[i]).as_long()
        meeting_start = arrival_time if arrival_time >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival_time)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")