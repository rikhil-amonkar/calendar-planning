from z3 import *

# Define the travel times in minutes
travel_times = {
    'Bayview': {'Union Square': 17, 'Presidio': 31},
    'Union Square': {'Bayview': 15, 'Presidio': 24},
    'Presidio': {'Bayview': 31, 'Union Square': 22}
}

# Define the arrival and departure times for each location
arrival_times = {
    'Richard': {'start': 8*60 + 45, 'end': 1*60 + 0},
    'Charles': {'start': 9*60 + 45, 'end': 1*60 + 0}
}

# Define the minimum meeting times in minutes
min_meeting_times = {
    'Richard': 2*60 + 0,
    'Charles': 2*60 + 0
}

# Define the solver
s = Solver()

# Define the variables
x = [Bool(f'meet_{i}') for i in ['Richard', 'Charles']]
y = [Int(f'time_{i}') for i in ['Richard', 'Charles']]

# Define the constraints
for i in range(len(x)):
    s.add(y[i] >= 9*60)  # Ensure that Richard and Charles are met after 9:00AM
    s.add(y[i] <= arrival_times[list(arrival_times.keys())[i]]['end'])

# Define the constraints for meeting times
for i in range(len(x)):
    s.add(x[i] == True == (y[i] + min_meeting_times[list(min_meeting_times.keys())[i]] <= arrival_times[list(arrival_times.keys())[i]]['end']))

# Define the constraints for travel times
s.add(x[0] == True == (y[0] >= 0))  # Richard starts at Bayview
s.add(x[1] == True == (y[1] >= travel_times['Bayview']['Presidio']))  # Charles starts at Presidio

# Define the objective function
s.add(x[0] + x[1] == Max(x[0], x[1]))

# Solve the problem
s.check()

# Get the solution
model = s.model()

# Print the solution
print("SOLUTION:")
if model[x[0]].as_bool():
    print(f"Meet Richard at {model[y[0]].as_long()} minutes after 9:00AM")
else:
    print("Do not meet Richard")

if model[x[1]].as_bool():
    print(f"Meet Charles at {model[y[1]].as_long()} minutes after 9:00AM")
else:
    print("Do not meet Charles")