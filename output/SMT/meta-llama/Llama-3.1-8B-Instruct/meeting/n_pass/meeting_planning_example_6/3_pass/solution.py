from z3 import *

# Define the travel times
travel_times = {
    'Fisherman\'s Wharf to Nob Hill': 11,
    'Nob Hill to Fisherman\'s Wharf': 11
}

# Define the constraints
start_time = 9 * 60  # 9:00 AM in minutes
kenneth_start = 2 * 60 + 15  # 2:15 PM in minutes
kenneth_end = 7 * 60 + 45  # 7:45 PM in minutes
min_meeting_time = 90  # 90 minutes

# Define the variables
x = Int('x')  # Time to leave Fisherman's Wharf
y = Int('y')  # Time to meet Kenneth at Nob Hill

# Define the solver
solver = Solver()

# Add constraints
solver.add(x >= start_time)  # Leave Fisherman's Wharf after 9:00 AM
solver.add(y >= x + travel_times['Fisherman\'s Wharf to Nob Hill'])  # Travel to Nob Hill
solver.add(y <= kenneth_end)  # Meet Kenneth before 7:45 PM
solver.add(kenneth_start <= y)  # Meet Kenneth after 2:15 PM
solver.add(y - x >= min_meeting_time)  # Meet Kenneth for at least 90 minutes

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print(f"Optimal schedule: Leave Fisherman's Wharf at {model[x] // 60}:{model[x] % 60} AM, meet Kenneth at Nob Hill at {model[y] // 60}:{model[y] % 60} PM")
else:
    print("No solution found")

# Check for optimal schedule
optimal_schedule = None
optimal_time = float('inf')
for x_val in range(start_time, kenneth_start):
    for y_val in range(x_val + travel_times['Fisherman\'s Wharf to Nob Hill'], kenneth_end):
        if kenneth_start <= y_val <= kenneth_end and y_val - x_val >= min_meeting_time:
            travel_time = x_val + travel_times['Fisherman\'s Wharf to Nob Hill'] + (y_val - x_val - travel_times['Fisherman\'s Wharf to Nob Hill'])
            if travel_time < optimal_time:
                optimal_time = travel_time
                optimal_schedule = (x_val, y_val)

if optimal_schedule:
    print(f"Optimal schedule: Leave Fisherman's Wharf at {optimal_schedule[0] // 60}:{optimal_schedule[0] % 60} AM, meet Kenneth at Nob Hill at {optimal_schedule[1] // 60}:{optimal_schedule[1] % 60} PM")