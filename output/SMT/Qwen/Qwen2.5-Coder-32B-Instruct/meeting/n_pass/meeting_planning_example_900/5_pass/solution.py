from z3 import *

# Define the time slots in minutes since 9:00 AM
start_time = 0
end_time = 600  # 10:00 PM

# Define the friends' availability
friends_availability = {
    "Matthew": (390, 480),  # 4:30 PM to 8:00 PM
    "Rebecca": (255, 450),  # 3:15 PM to 7:15 PM
    "Brian": (135, 600),   # 2:15 PM to 10:00 PM
    "Emily": (69, 465),    # 11:15 AM to 7:45 PM
    "Karen": (75, 330),    # 11:45 AM to 5:30 PM
    "Stephanie": (90, 225), # 1:00 PM to 3:45 PM
    "James": (150, 420),   # 2:30 PM to 7:00 PM
    "Steven": (120, 480),  # 2:00 PM to 8:00 PM
    "Elizabeth": (90, 315),# 1:00 PM to 5:15 PM
    "William": (375, 495)  # 6:15 PM to 8:15 PM
}

# Define the minimum meeting times
min_meeting_times = {
    "Matthew": 45,
    "Rebecca": 105,
    "Brian": 30,
    "Emily": 15,
    "Karen": 30,
    "Stephanie": 75,
    "James": 120,
    "Steven": 30,
    "Elizabeth": 120,
    "William": 90
}

# Define the travel times between locations
travel_times = {
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Bayview"): 19,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Bayview"): 27,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 20,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Bayview"): 16,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16
}

# Create the solver
solver = Solver()

# Define the variables for each friend's meeting time
meeting_start_times = {friend: Int(f"start_{friend}") for friend in friends_availability}
meeting_end_times = {friend: Int(f"end_{friend}") for friend in friends_availability}

# Add constraints for each friend
for friend, (avail_start, avail_end) in friends_availability.items():
    min_meeting_time = min_meeting_times[friend]
    solver.add(meeting_start_times[friend] >= avail_start)
    solver.add(meeting_start_times[friend] <= avail_end - min_meeting_time)
    solver.add(meeting_end_times[friend] >= meeting_start_times[friend] + min_meeting_time)
    solver.add(meeting_end_times[friend] <= avail_end)

# Define the sequence of visits
friends_list = list(friends_availability.keys())
num_friends = len(friends_list)
visited = [Bool(f"visited_{i}") for i in range(num_friends)]

# Define the order of visits
order_vars = [Int(f"order_{i}") for i in range(8)]  # Exactly 8 friends
for i in range(8):
    solver.add(order_vars[i] >= 0)
    solver.add(order_vars[i] < num_friends)
    solver.add(Distinct(order_vars[:i+1]))

# Ensure each friend is visited at most once
for i in range(num_friends):
    solver.add(Sum([If(order_vars[j] == i, 1, 0) for j in range(8)]) <= 1)

# Define the current location and time
current_location = String("current_location")
current_time = Int("current_time")

# Initialize the starting point
solver.add(current_location == "Richmond District")
solver.add(current_time == 0)

# Add constraints for transitions
for i in range(8):
    if i == 0:
        friend_i = friends_list[model[order_vars[i]].as_long()]
        travel_time = travel_times.get(("Richmond District", friend_i), float('inf'))
        solver.add(meeting_start_times[friend_i] >= travel_time)
    else:
        friend_i = friends_list[model[order_vars[i-1]].as_long()]
        friend_j = friends_list[model[order_vars[i]].as_long()]
        travel_time = travel_times.get((friend_i, friend_j), float('inf'))
        solver.add(meeting_end_times[friend_i] + travel_time <= meeting_start_times[friend_j])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for i in range(8):
        friend_index = model[order_vars[i]].as_long()
        friend = friends_list[friend_index]
        start = model[meeting_start_times[friend]].as_long()
        end = model[meeting_end_times[friend]].as_long()
        schedule.append((friend, start, end))
    schedule.sort(key=lambda x: x[1])
    print("SOLUTION:")
    for friend, start, end in schedule:
        print(f"{friend}: {start//60}:{start%60:02} - {end//60}:{end%60:02}")
else:
    print("No solution found.")