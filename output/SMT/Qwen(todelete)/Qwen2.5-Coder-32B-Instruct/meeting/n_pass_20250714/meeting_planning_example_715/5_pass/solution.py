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
    "Amanda": ("Marina District", 1485, 105),  # 2:45PM to 7:30PM, 105 minutes
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

# Number of friends to visit
num_friends_to_visit = 7

# Define the sequence of visits
visit_sequence = [String(f'visit_{i}') for i in range(num_friends_to_visit)]
visit_start_times = [Int(f'visit_start_{i}') for i in range(num_friends_to_visit)]
visit_end_times = [Int(f'visit_end_{i}') for i in range(num_friends_to_visit)]

# Initial conditions
solver.add(visit_sequence[0] == "Presidio")
solver.add(visit_start_times[0] == 540)  # 9:00AM

# Add constraints for each visit
for i in range(num_friends_to_visit):
    friend = visit_sequence[i]
    location = String(f'location_{i}')
    available_start = Int(f'available_start_{i}')
    duration = Int(f'duration_{i}')
    travel_time = Int(f'travel_time_{i}')

    # Map the visit sequence to friends
    solver.add(Or([friend == f for f in friends_availability.keys()]))

    # Get the location, available start time, and duration for the friend
    solver.add(And(
        [Implies(friend == f, And(location == friends_availability[f][0],
                                  available_start == friends_availability[f][1],
                                  duration == friends_availability[f][2]))
         for f in friends_availability.keys()]
    ))

    # Add constraints for the visit
    solver.add(visit_start_times[i] >= available_start)
    solver.add(visit_end_times[i] <= available_start + 690)  # End of the day is 9:30PM
    solver.add(visit_end_times[i] == visit_start_times[i] + duration)
    if i > 0:
        solver.add(travel_time == travel_times[(visit_sequence[i-1].as_string().replace('"', ''), location.as_string().replace('"', ''))])
        solver.add(visit_start_times[i] >= visit_end_times[i-1] + travel_time)

    # Ensure unique visits
    if i > 0:
        solver.add(And([visit_sequence[i] != visit_sequence[j] for j in range(i)]))

# Ensure exactly 7 friends are visited
solver.add(Distinct(visit_sequence))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for i in range(num_friends_to_visit):
        friend = model.evaluate(visit_sequence[i]).as_string().replace('"', '')
        location = friends_availability[friend][0]
        visit_start = model.evaluate(visit_start_times[i])
        visit_end = model.evaluate(visit_end_times[i])
        print(f"Meet {friend} at {location} from {visit_start} to {visit_end}")
else:
    print("No solution found.")