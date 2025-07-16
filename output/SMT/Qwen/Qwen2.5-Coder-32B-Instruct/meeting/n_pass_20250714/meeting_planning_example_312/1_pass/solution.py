from z3 import *

# Define the time variables for each friend
sarah_start = Int('sarah_start')
richard_start = Int('richard_start')
elizabeth_start = Int('elizabeth_start')
michelle_start = Int('michelle_start')

# Define the travel times between districts
travel_times = {
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
}

# Create a solver instance
solver = Solver()

# Add constraints for meeting times
solver.add(sarah_start >= 645)  # 10:45 AM in minutes
solver.add(sarah_start + 30 <= 420)  # Must finish by 7:00 PM (420 minutes)

solver.add(richard_start >= 705)  # 11:45 AM in minutes
solver.add(richard_start + 90 <= 225)  # Must finish by 3:45 PM (225 minutes)

solver.add(elizabeth_start >= 660)  # 11:00 AM in minutes
solver.add(elizabeth_start + 120 <= 315)  # Must finish by 5:15 PM (315 minutes)

solver.add(michelle_start >= 375)  # 6:15 PM in minutes
solver.add(michelle_start + 90 <= 525)  # Must finish by 8:45 PM (525 minutes)

# Define the current location and start time
current_location = 'Richmond District'
start_time = 540  # 9:00 AM in minutes

# Function to add travel constraints
def add_travel_constraints(current_location, next_location, next_start):
    travel_time = travel_times[(current_location, next_location)]
    solver.add(next_start >= start_time + travel_time)

# Try to visit all friends in a feasible order
# This is a simple approach; a more sophisticated approach would involve permutations or graph traversal
add_travel_constraints(current_location, 'Sunset District', sarah_start)
add_travel_constraints('Sunset District', 'Haight-Ashbury', richard_start)
add_travel_constraints('Haight-Ashbury', 'Mission District', elizabeth_start)
add_travel_constraints('Mission District', 'Golden Gate Park', michelle_start)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        'Sarah': model[sarah_start].as_long(),
        'Richard': model[richard_start].as_long(),
        'Elizabeth': model[elizabeth_start].as_long(),
        'Michelle': model[michelle_start].as_long(),
    }
    print("SOLUTION:")
    for friend, start_time in solution.items():
        print(f"Meet {friend} at {start_time // 60}:{start_time % 60:02d} PM")
else:
    print("No feasible schedule found.")