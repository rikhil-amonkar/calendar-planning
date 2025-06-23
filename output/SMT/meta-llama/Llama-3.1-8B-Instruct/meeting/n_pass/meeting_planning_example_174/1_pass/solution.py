from z3 import *

# Define the travel distances in minutes
travel_distances = {
    'Nob_Hill': {'Pacific_Heights': 8, 'Mission_District': 13},
    'Pacific_Heights': {'Nob_Hill': 8, 'Mission_District': 15},
    'Mission_District': {'Nob_Hill': 12, 'Pacific_Heights': 16}
}

# Define the arrival and departure times
arrival_time = 9 * 60  # 9:00 AM
thomas_arrival = 3 * 60 + 30  # 3:30 PM
thomas_departure = 7 * 60 + 15  # 7:15 PM
kenneth_arrival = 12 * 60  # 12:00 PM
kenneth_departure = 3 * 60 + 45  # 3:45 PM

# Define the minimum meeting times
min_meeting_time_thomas = 75
min_meeting_time_kenneth = 45

# Define the solver
solver = Solver()

# Define the variables
x_nob_to_pacific = Bool('x_nob_to_pacific')
x_nob_to_mission = Bool('x_nob_to_mission')
x_pacific_to_nob = Bool('x_pacific_to_nob')
x_pacific_to_mission = Bool('x_pacific_to_mission')
x_mission_to_nob = Bool('x_mission_to_nob')
x_mission_to_pacific = Bool('x_mission_to_pacific')

# Add the variables to the solver
solver.add([x_nob_to_pacific, x_nob_to_mission, x_pacific_to_nob, x_pacific_to_mission, x_mission_to_nob, x_mission_to_pacific])

# Define the constraints
# Thomas must be met between 3:30 PM and 7:15 PM
solver.add(And(thomas_arrival <= If(x_pacific_to_nob, arrival_time + travel_distances['Nob_Hill']['Pacific_Heights'], arrival_time), 
              If(x_pacific_to_nob, arrival_time + travel_distances['Nob_Hill']['Pacific_Heights'] + min_meeting_time_thomas, thomas_arrival) <= thomas_departure))

# Kenneth must be met between 12:00 PM and 3:45 PM
solver.add(And(kenneth_arrival <= If(x_mission_to_nob, arrival_time + travel_distances['Nob_Hill']['Mission_District'], arrival_time), 
              If(x_mission_to_nob, arrival_time + travel_distances['Nob_Hill']['Mission_District'] + min_meeting_time_kenneth, kenneth_arrival) <= kenneth_departure))

# If we meet Thomas, we cannot meet Kenneth
solver.add(Or(Not(x_pacific_to_nob), Not(x_mission_to_nob)))

# If we meet Kenneth, we cannot meet Thomas
solver.add(Or(Not(x_mission_to_nob), Not(x_pacific_to_nob)))

# Solve the solver
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    if model[x_nob_to_pacific]:
        print("Meet Thomas at Pacific Heights")
    else:
        print("Do not meet Thomas at Pacific Heights")
    if model[x_nob_to_mission]:
        print("Meet Kenneth at Mission District")
    else:
        print("Do not meet Kenneth at Mission District")
else:
    print("No solution found")