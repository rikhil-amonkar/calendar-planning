from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Richmond District"): 14,

    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Richmond District"): 12,

    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Richmond District"): 18,

    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Richmond District"): 7,

    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,

    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Richmond District"): 10,

    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Richmond District"): 18,

    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Richmond District"): 20,

    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Richmond District"): 11,

    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Richmond District"): 25,

    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27
}

# Define friend meeting details.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You arrive at Russian Hill at 9:00AM = 540.
friends = [
    # Emily: at Pacific Heights from 9:15AM (555) to 1:45PM (825); meeting >= 120 minutes.
    ("Pacific Heights", 555, 825, 120),
    # Helen: at North Beach from 1:45PM (825) to 6:45PM (1125); meeting >= 30 minutes.
    ("North Beach", 825, 1125, 30),
    # Kimberly: at Golden Gate Park from 6:45PM (1125) to 9:15PM (1275); meeting >= 75 minutes.
    ("Golden Gate Park", 1125, 1275, 75),
    # James: at Embarcadero from 10:30AM (630) to 11:30AM (690); meeting >= 30 minutes.
    ("Embarcadero", 630, 690, 30),
    # Linda: at Haight-Ashbury from 7:30AM (450) to 7:15PM (1155); meeting >= 15 minutes.
    ("Haight-Ashbury", 450, 1155, 15),
    # Paul: at Fisherman's Wharf from 2:45PM (885) to 6:45PM (1125); meeting >= 90 minutes.
    ("Fisherman's Wharf", 885, 1125, 90),
    # Anthony: at Mission District from 8:00AM (480) to 2:45PM (885); meeting >= 105 minutes.
    ("Mission District", 480, 885, 105),
    # Nancy: at Alamo Square from 8:30AM (510) to 1:45PM (825); meeting >= 120 minutes.
    ("Alamo Square", 510, 825, 120),
    # William: at Bayview from 5:30PM (1050) to 8:30PM (1230); meeting >= 120 minutes.
    ("Bayview", 1050, 1230, 120),
    # Margaret: at Richmond District from 3:15PM (915) to 6:15PM (1095); meeting >= 45 minutes.
    ("Richmond District", 915, 1095, 45)
]
friend_names = ["Emily", "Helen", "Kimberly", "James", "Linda", "Paul", "Anthony", "Nancy", "William", "Margaret"]
num_friends = len(friends)

# Starting location and time.
start_loc = "Russian Hill"
start_time = 540  # 9:00AM

# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# For each friend i:
#   x[i]    : Boolean indicating if friend i is scheduled.
#   A[i]    : Arrival time at friend i's location.
#   order[i]: The index of the meeting in the itinerary (if scheduled, in [0, num_friends-1], else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled then order[i] is in [0, num_friends-1], otherwise -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure distinct order values for scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Each scheduled meeting must fit inside the friend’s available time window.
# The meeting begins at the later of your arrival time and the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For any scheduled meeting i with order 0, your arrival time must be at least
# the start_time plus travel time from the starting location to friend i's location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# Travel constraints between consecutive meetings:
# If meeting j immediately follows meeting i (order[j] == order[i]+1), then your arrival time at j
# must be at least the departure time from i plus the travel time from i's location to j's location.
# The departure time from meeting i is defined as max(A[i], avail_start_i) + min_duration_i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time))

# The objective is to maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            scheduled.append((model.evaluate(order[i]).as_long(), i))
    scheduled.sort()
    
    print("Optimal meeting schedule:")
    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in scheduled:
        loc, avail_start, avail_end, dur = friends[i]
        arr = model.evaluate(A[i]).as_long()
        # The meeting starts at the later of arrival time and available start.
        meet_start = arr if arr >= avail_start else avail_start
        meet_end = meet_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arr)}")
        print(f"    Meeting from {to_time(meet_start)} to {to_time(meet_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")