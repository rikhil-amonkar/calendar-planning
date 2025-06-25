from z3 import *

# Define the travel times
travel_times = {
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Mission District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Pacific Heights'): 16
}

# Define the constraints
s = Optimize()

# Define the variables
x_nob_to_pacific = Bool('x_nob_to_pacific')
x_nob_to_mission = Bool('x_nob_to_mission')
x_pacific_to_nob = Bool('x_pacific_to_nob')
x_pacific_to_mission = Bool('x_pacific_to_mission')
x_mission_to_nob = Bool('x_mission_to_nob')
x_mission_to_pacific = Bool('x_mission_to_pacific')

# Define the objective function
obj = If(x_nob_to_pacific, 1, 0) + If(x_nob_to_mission, 1, 0) + If(x_pacific_to_nob, 1, 0) + If(x_pacific_to_mission, 1, 0) + If(x_mission_to_nob, 1, 0) + If(x_mission_to_pacific, 1, 0)

# Define the constraints
s.add(If(x_nob_to_pacific, 1, 0) + If(x_nob_to_mission, 1, 0) >= 1)  # Must visit at least one location
s.add(If(x_pacific_to_nob, 1, 0) + If(x_pacific_to_mission, 1, 0) + If(x_mission_to_nob, 1, 0) + If(x_mission_to_pacific, 1, 0) >= 1)  # Must visit at least one location
s.add(If(x_nob_to_pacific, 1, 0) + If(x_nob_to_mission, 1, 0) + If(x_pacific_to_nob, 1, 0) + If(x_pacific_to_mission, 1, 0) + If(x_mission_to_nob, 1, 0) + If(x_mission_to_pacific, 1, 0) >= 2)  # Must visit at least two locations

s.add(If(x_nob_to_pacific, 1, 0) * (3*60 + 30 - 9*60) >= 75)  # Must meet Thomas for at least 75 minutes
s.add(If(x_nob_to_mission, 1, 0) * (3*60 + 45 - 9*60) >= 45)  # Must meet Kenneth for at least 45 minutes

# Define the objective
s.minimize(obj)

# Solve the problem
s.check()

# Get the solution
model = s.model()

# Print the solution
print("SOLUTION:")
if model[x_nob_to_pacific]:
    print("Visit Pacific Heights")
if model[x_nob_to_mission]:
    print("Visit Mission District")
if model[x_pacific_to_nob]:
    print("Visit Pacific Heights from Nob Hill")
if model[x_pacific_to_mission]:
    print("Visit Mission District from Pacific Heights")
if model[x_mission_to_nob]:
    print("Visit Nob Hill from Mission District")
if model[x_mission_to_pacific]:
    print("Visit Pacific Heights from Mission District")

# Calculate the total travel time
total_travel_time = 0
if model[x_nob_to_pacific]:
    total_travel_time += travel_times[('Nob Hill', 'Pacific Heights')]
if model[x_nob_to_mission]:
    total_travel_time += travel_times[('Nob Hill', 'Mission District')]
if model[x_pacific_to_nob]:
    total_travel_time += travel_times[('Pacific Heights', 'Nob Hill')]
if model[x_pacific_to_mission]:
    total_travel_time += travel_times[('Pacific Heights', 'Mission District')]
if model[x_mission_to_nob]:
    total_travel_time += travel_times[('Mission District', 'Nob Hill')]
if model[x_mission_to_pacific]:
    total_travel_time += travel_times[('Mission District', 'Pacific Heights')]

print("Total travel time: ", total_travel_time, " minutes")