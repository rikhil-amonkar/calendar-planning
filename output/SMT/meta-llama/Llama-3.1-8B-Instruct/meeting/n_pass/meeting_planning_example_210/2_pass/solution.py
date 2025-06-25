YOUR_CODE
from z3 import *

# Define the variables
time = [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
locations = ['Fisherman\'s Wharf', 'Presidio', 'Richmond District', 'Financial District']
friends = ['Emily', 'Joseph', 'Melissa']
travel_times = {
    'Fisherman\'s Wharf': {'Presidio': 19, 'Richmond District': 18, 'Financial District': 11},
    'Presidio': {'Fisherman\'s Wharf': 17, 'Richmond District': 7, 'Financial District': 23},
    'Richmond District': {'Fisherman\'s Wharf': 18, 'Presidio': 7, 'Financial District': 22},
    'Financial District': {'Fisherman\'s Wharf': 10, 'Presidio': 22, 'Richmond District': 21}
}
min_meeting_time = {'Emily': 105, 'Joseph': 120, 'Melissa': 75}
friend_availability = {
    'Emily': [4*60 + 15, 9*60],  # 4:15PM to 9:00PM
    'Joseph': [5*60 + 15, 10*60],  # 5:15PM to 10:00PM
    'Melissa': [3*60 + 45, 9*60 + 45]  # 3:45PM to 9:45PM
}

# Create the solver
s = Solver()

# Define the variables
x = [[Bool(f'x_{i}_{j}') for j in locations] for i in time]
y = [[Bool(f'y_{i}_{j}') for j in friends] for i in time]

# Add constraints
for i in time:
    # Each location can only be visited once
    s.add(Or([Not(x[i][j]) for j in range(len(locations))]))
    # Each friend can only be met once
    s.add(Or([Not(y[i][j]) for j in range(len(friends))]))
    # Meet Emily for at least 105 minutes
    if i >= 4*60 + 15 and i <= 9*60:
        s.add(y[i][friends.index('Emily')])
    else:
        s.add(Not(y[i][friends.index('Emily')]))
    # Meet Joseph for at least 120 minutes
    if i >= 5*60 + 15 and i <= 10*60:
        s.add(y[i][friends.index('Joseph')])
    else:
        s.add(Not(y[i][friends.index('Joseph')]))
    # Meet Melissa for at least 75 minutes
    if i >= 3*60 + 45 and i <= 9*60 + 45:
        s.add(y[i][friends.index('Melissa')])
    else:
        s.add(Not(y[i][friends.index('Melissa')]))

# Add constraints for travel times
for i in time:
    for j in range(len(locations)):
        if i > 9*60:  # After 9:00PM, no more travel
            s.add(Not(x[i][j]))
        else:
            for k in range(len(locations)):
                s.add(Implies(x[i][j], Not(x[i][k])))
            for friend in friends:
                if i + travel_times[locations[j]][locations[k]] >= friend_availability[friend][0] and i + travel_times[locations[j]][locations[k]] <= friend_availability[friend][1]:
                    s.add(Implies(x[i][j], y[i + travel_times[locations[j]][locations[k]]][friends.index(friend)]))

# Add objective function
objective = [[If(x[i][j], 1, 0) + If(y[i][j], 1, 0) for j in range(len(locations) + len(friends))] for i in time]
s.set_objective(Maximize(Sum([item for sublist in objective for item in sublist])))

# Solve the problem
if s.check() == sat:
    model = s.model()
    print("SOLUTION:")
    for i in time:
        for j in range(len(locations)):
            if model.evaluate(x[i][j]).as_bool():
                print(f"At {i/60} hours, visit {locations[j]}")
        for j in range(len(friends)):
            if model.evaluate(y[i][j]).as_bool():
                print(f"At {i/60} hours, meet {friends[j]}")
else:
    print("No solution exists")