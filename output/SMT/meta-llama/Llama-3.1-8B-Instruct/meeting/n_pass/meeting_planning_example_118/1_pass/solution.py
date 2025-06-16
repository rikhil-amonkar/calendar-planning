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
for i in ['Richard', 'Charles']:
    s.add(y[i] >= arrival_times[i]['start'])
    s.add(y[i] <= arrival_times[i]['end'])

for i in ['Richard', 'Charles']:
    s.add(y[i] >= 0)

# Define the constraints for meeting times
for i in ['Richard', 'Charles']:
    s.add(x[i] == True == (y[i] + min_meeting_times[i] <= arrival_times[i]['end']))

# Define the constraints for travel times
for i in ['Richard', 'Charles']:
    s.add(x[i] == True == (y[i] - travel_times['Bayview']['Union Square'] >= 0))

# Define the objective function
s.add(x['Richard'] + x['Charles'] == Max(x['Richard'], x['Charles']))

# Solve the problem
s.check()

# Get the solution
model = s.model()

# Print the solution
print("SOLUTION:")
if model[x['Richard']].as_bool():
    print(f"Meet Richard at {model[y['Richard']].as_long()} minutes after 9:00AM")
else:
    print("Do not meet Richard")

if model[x['Charles']].as_bool():
    print(f"Meet Charles at {model[y['Charles']].as_long()} minutes after 9:00AM")
else:
    print("Do not meet Charles")