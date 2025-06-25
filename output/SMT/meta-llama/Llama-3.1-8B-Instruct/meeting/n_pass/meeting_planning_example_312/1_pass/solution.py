from z3 import *

# Define the travel distances in minutes
travel_distances = {
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
    ('Golden Gate Park', 'Mission District'): 17
}

# Define the friends and their availability
friends = {
    'Sarah': (10*60 + 45, 7*60),  # 10:45 AM - 7:00 PM
    'Richard': (11*60 + 45, 3*60 + 45),  # 11:45 AM - 3:45 PM
    'Elizabeth': (11*60, 5*60 + 15),  # 11:00 AM - 5:15 PM
    'Michelle': (6*60 + 15, 8*60 + 45)  # 6:15 PM - 8:45 PM
}

# Define the minimum meeting times
min_meeting_times = {
    'Sarah': 30,
    'Richard': 90,
    'Elizabeth': 120,
    'Michelle': 90
}

# Define the solver
solver = Optimize()

# Define the variables
x = [Bool(f"visit_{i}") for i in friends]
t = [Int(f"time_{i}") for i in friends]

# Define the constraints
for i, friend in enumerate(friends):
    solver.add(t[i] >= friends[friend][0])
    solver.add(t[i] <= friends[friend][1])
    solver.add(t[i] >= 9*60)  # You arrive at Richmond District at 9:00 AM
    if i == 0:  # Sarah
        solver.add(t[i] + min_meeting_times[friend] >= friends[friend][0])
        solver.add(t[i] + min_meeting_times[friend] <= friends[friend][1])
    elif i == 1:  # Richard
        solver.add(t[i] + min_meeting_times[friend] >= friends[friend][0])
        solver.add(t[i] + min_meeting_times[friend] <= friends[friend][1])
    elif i == 2:  # Elizabeth
        solver.add(t[i] + min_meeting_times[friend] >= friends[friend][0])
        solver.add(t[i] + min_meeting_times[friend] <= friends[friend][1])
    elif i == 3:  # Michelle
        solver.add(t[i] + min_meeting_times[friend] >= friends[friend][0])
        solver.add(t[i] + min_meeting_times[friend] <= friends[friend][1])

# Define the objective function
solver.minimize(sum([x[i] * (t[i] + min_meeting_times[friend]) for i, friend in enumerate(friends)]))

# Solve the problem
solution = solver.check()

# Print the solution
if solution == sat:
    model = solver.model()
    print("SOLUTION:")
    for i, friend in enumerate(friends):
        if model.evaluate(x[i]):
            print(f"Visit {friend} at {model.evaluate(t[i]).as_long() // 60}:{model.evaluate(t[i]).as_long() % 60}")
else:
    print("No solution found")