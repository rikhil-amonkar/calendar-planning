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

# Define variables for the current location and time after each meeting
current_location = "Embarcadero"
current_time = 9*60  # Start at 9:00 AM

# Function to add constraints for traveling to a location and meeting a friend
def add_meeting_constraints(friend):
    global current_location, current_time
    location, start, end, duration = availability[friend]
    
    # Ensure the meeting starts within the friend's availability
    solver.add(start_times[friend] >= start)
    solver.add(start_times[friend] <= end - duration)
    
    # Ensure we can travel to the location in time for the meeting
    travel_time = travel_times[(current_location, location)]
    solver.add(current_time + travel_time <= start_times[friend])
    
    # Update current location and time after the meeting
    current_location = location
    current_time = start_times[friend] + duration

# Add constraints for each friend in the order we want to meet them
friends_order = ["Mary", "Kevin", "Stephanie", "Deborah", "Emily"]
for friend in friends_order:
    add_meeting_constraints(friend)

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