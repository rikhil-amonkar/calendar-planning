from z3 import *

# Define the locations
locations = [
    "Presidio", "Marina District", "The Castro", "Fisherman's Wharf",
    "Bayview", "Pacific Heights", "Mission District", "Alamo Square",
    "Golden Gate Park"
]

# Define the travel times in minutes
travel_times = {
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Golden Gate Park"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Golden Gate Park"): 22,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Golden Gate Park"): 17,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
}

# Define the friends' availability
friends_availability = {
    "Amanda": ("Marina District", 1485, 450),  # 2:45PM to 7:30PM, 105 minutes
    "Melissa": ("The Castro", 570, 30),        # 9:30AM to 5:00PM, 30 minutes
    "Jeffrey": ("Fisherman's Wharf", 765, 120), # 12:45PM to 6:45PM, 120 minutes
    "Matthew": ("Bayview", 615, 30),           # 10:15AM to 1:15PM, 30 minutes
    "Nancy": ("Pacific Heights", 900, 105),     # 5:00PM to 9:30PM, 105 minutes
    "Karen": ("Mission District", 1050, 105),  # 5:30PM to 8:30PM, 105 minutes
    "Robert": ("Alamo Square", 675, 120),      # 11:15AM to 5:30PM, 120 minutes
    "Joseph": ("Golden Gate Park", 510, 105)   # 8:30AM to 9:15PM, 105 minutes
}

# Create a solver instance
solver = Solver()

# Define the decision variables
current_location = String('current_location')
start_time = Int('start_time')
visited = {friend: Bool(f'visited_{friend}') for friend in friends_availability}

# Initial conditions
solver.add(current_location == "Presidio")
solver.add(start_time == 540)  # 9:00AM

# Helper function to add constraints for visiting a friend
def add_visit_constraints(friend, location, available_start, duration):
    visit_start = Int(f'{friend}_visit_start')
    visit_end = Int(f'{friend}_visit_end')
    travel_time = Int(f'{friend}_travel_time')

    solver.add(visit_start >= available_start)
    solver.add(visit_end <= available_start + 690)  # End of the day is 9:30PM
    solver.add(visit_end == visit_start + duration)
    solver.add(travel_time == travel_times[(current_location, location)])
    solver.add(start_time + travel_time <= visit_start)

    # Update current location and start time after visiting
    solver.add(If(visited[friend], And(current_location == location, start_time == visit_end), True))

# Add constraints for each friend
for friend, (location, available_start, duration) in friends_availability.items():
    solver.add(If(visited[friend], add_visit_constraints(friend, location, available_start, duration), True))

# Maximize the number of friends visited
objective = Sum([If(visited[friend], 1, 0) for friend in friends_availability])
solver.maximize(objective)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in friends_availability:
        if model.evaluate(visited[friend]):
            print(f"Meet {friend} at {friends_availability[friend][0]} from {model.evaluate(Int(f'{friend}_visit_start'))} to {model.evaluate(Int(f'{friend}_visit_end'))}")
else:
    print("No solution found.")