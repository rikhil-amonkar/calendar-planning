from z3 import *

# Define the locations
locations = ["Embarcadero", "Golden Gate Park", "Haight-Ashbury", "Bayview", "Presidio", "Financial District"]

# Define the travel times in minutes
travel_times = {
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Financial District"): 19,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Financial District"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Presidio"): 22,
}

# Define the friends' availability
availability = {
    "Mary": ("Golden Gate Park", 8*60 + 45, 11*60 + 45, 45),
    "Kevin": ("Haight-Ashbury", 10*60 + 15, 16*60 + 15, 90),
    "Deborah": ("Bayview", 15*60, 19*60 + 15, 120),
    "Stephanie": ("Presidio", 10*60, 17*60 + 15, 120),
    "Emily": ("Financial District", 11*60 + 30, 21*60 + 45, 105),
}

# Create a solver instance
solver = Solver()

# Define variables for the start time of meeting each friend
start_times = {friend: Int(f"start_{friend}") for friend in availability}

# Add constraints for each friend
for friend, (location, start, end, duration) in availability.items():
    # Ensure the meeting starts within the friend's availability
    solver.add(start_times[friend] >= start)
    solver.add(start_times[friend] <= end - duration)

# Define a variable for the current location
current_location = String("current_location")
solver.add(current_location == "Embarcadero")

# Define a variable for the current time
current_time = Int("current_time")
solver.add(current_time == 9*60)  # Start at 9:00 AM

# Function to add constraints for traveling to a location and meeting a friend
def add_meeting_constraints(friend, prev_friend=None):
    location, start, end, duration = availability[friend]
    if prev_friend is None:
        # First meeting, just ensure we can get there in time
        solver.add(current_time + travel_times[(current_location.as_string(), location)] <= start_times[friend])
        solver.add(start_times[friend] + duration <= end)
        solver.add(current_location == location)
        solver.add(current_time == start_times[friend] + duration)
    else:
        # Subsequent meetings, ensure we can travel and meet in time
        prev_location, _, _, _ = availability[prev_friend]
        solver.add(current_time + travel_times[(prev_location, location)] <= start_times[friend])
        solver.add(start_times[friend] + duration <= end)
        solver.add(current_location == location)
        solver.add(current_time == start_times[friend] + duration)

# Add constraints for each friend in the order we want to meet them
friends_order = ["Mary", "Kevin", "Stephanie", "Deborah", "Emily"]
for i, friend in enumerate(friends_order):
    if i == 0:
        add_meeting_constraints(friend)
    else:
        add_meeting_constraints(friend, friends_order[i-1])

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    SOLUTION = []
    for friend in friends_order:
        start = model.evaluate(start_times[friend]).as_long()
        hours, minutes = divmod(start, 60)
        SOLUTION.append(f"Meet {friend} at {hours:02}:{minutes:02}")
    print("SOLUTION:")
    for line in SOLUTION:
        print(line)
else:
    print("No solution found.")