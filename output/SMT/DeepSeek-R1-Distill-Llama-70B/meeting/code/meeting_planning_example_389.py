from z3 import *

# Define the friends and their constraints
friends = ['Mary', 'Sarah', 'Thomas', 'Helen']

# Convert times to minutes since midnight
def to_minutes(hours, minutes):
    return hours * 60 + minutes

# Mary's constraints
mary_start = 13 * 60  # 1:00 PM
mary_end = 19 * 60 + 15  # 7:15 PM
mary_duration = 75

# Sarah's constraints
sarah_start = 14 * 60 + 45  # 2:45 PM
sarah_end = 17 * 60 + 30  # 5:30 PM
sarah_duration = 105

# Thomas's constraints
thomas_start = 15 * 60 + 15  # 3:15 PM
thomas_end = 18 * 60 + 45  # 6:45 PM
thomas_duration = 120

# Helen's constraints
helen_start = 21 * 60 + 45  # 9:45 PM
helen_end = 22 * 60 + 30  # 10:30 PM
helen_duration = 30

# Travel times in minutes (from the current location to the next)
travel_times = {
    'Haight': {'Richmond': 10, 'Fishermans': 23, 'Mission': 11, 'Bayview': 18},
    'Richmond': {'Fishermans': 18, 'Haight': 10, 'Mission': 20, 'Bayview': 26},
    'Fishermans': {'Richmond': 18, 'Haight': 22, 'Mission': 22, 'Bayview': 26},
    'Mission': {'Haight': 12, 'Fishermans': 22, 'Richmond': 20, 'Bayview': 15},
    'Bayview': {'Haight': 19, 'Fishermans': 25, 'Richmond': 25, 'Mission': 13}
}

# Define the sequence of locations to visit based on the initial plan
sequence = ['Richmond', 'Fishermans', 'Bayview', 'Mission']

# Create variables for each friend's start and end times
S = {}
E = {}

for friend in friends:
    S[friend] = Int(f'S_{friend}')
    E[friend] = Int(f'E_{friend}')

# Add constraints for each friend
constraints = []

# Mary's constraints
constraints.append(S['Mary'] >= mary_start)
constraints.append(E['Mary'] <= mary_end)
constraints.append(E['Mary'] - S['Mary'] >= mary_duration)

# Sarah's constraints
constraints.append(S['Sarah'] >= sarah_start)
constraints.append(E['Sarah'] <= sarah_end)
constraints.append(E['Sarah'] - S['Sarah'] >= sarah_duration)

# Thomas's constraints
constraints.append(S['Thomas'] >= thomas_start)
constraints.append(E['Thomas'] <= thomas_end)
constraints.append(E['Thomas'] - S['Thomas'] >= thomas_duration)

# Helen's constraints
constraints.append(S['Helen'] >= helen_start)
constraints.append(E['Helen'] <= helen_end)
constraints.append(E['Helen'] - S['Helen'] >= helen_duration)

# Travel time constraints based on the sequence
# Starting from Haight at 9:00 AM (540 minutes)
current_time = 540  # 9:00 AM

for i in range(len(sequence)):
    location = sequence[i]
    if i == 0:
        # From Haight to Richmond
        travel = travel_times['Haight'][location]
        constraints.append(S['Mary'] >= current_time + travel)
        current_time = S['Mary']
    elif i == 1:
        # From Richmond to Fishermans
        travel = travel_times['Richmond'][location]
        constraints.append(S['Sarah'] >= E['Mary'] + travel)
        current_time = S['Sarah']
    elif i == 2:
        # From Fishermans to Bayview
        travel = travel_times['Fishermans'][location]
        constraints.append(S['Thomas'] >= E['Sarah'] + travel)
        current_time = S['Thomas']
    elif i == 3:
        # From Bayview to Mission
        travel = travel_times['Bayview'][location]
        constraints.append(S['Helen'] >= E['Thomas'] + travel)
        current_time = S['Helen']

# Solve the problem
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend in friends:
        print(f"Meet {friend} from {model[S[friend]].as_string()} to {model[E[friend]].as_string()}")
else:
    print("No solution found.")