from z3 import *

# Define travel times between locations
travel_dict = {
    'Marina District': {
        'Richmond District': 11,
        'Union Square': 16,
        'Nob Hill': 12,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Financial District': 17,
        'North Beach': 11,
        'Presidio': 10
    },
    'Richmond District': {
        'Marina District': 9,
        'Union Square': 21,
        'Nob Hill': 17,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'North Beach': 17,
        'Presidio': 7
    },
    'Union Square': {
        'Marina District': 18,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Fisherman\'s Wharf': 15,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Financial District': 9,
        'North Beach': 10,
        'Presidio': 24
    },
    'Nob Hill': {
        'Marina District': 11,
        'Richmond District': 14,
        'Union Square': 7,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Financial District': 9,
        'North Beach': 8,
        'Presidio': 17
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Financial District': 11,
        'North Beach': 6,
        'Presidio': 17
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 20,
        'Fisherman\'s Wharf': 24,
        'Embarcadero': 25,
        'Financial District': 26,
        'North Beach': 23,
        'Presidio': 11
    },
    'Embarcadero': {
        'Marina District': 12,
        'Richmond District': 21,
        'Union Square': 10,
        'Nob Hill': 10,
        'Fisherman\'s Wharf': 6,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20
    },
    'Financial District': {
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Nob Hill': 8,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'North Beach': 7,
        'Presidio': 22
    },
    'North Beach': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 7,
        'Nob Hill': 7,
        'Fisherman\'s Wharf': 5,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Financial District': 8,
        'Presidio': 17
    },
    'Presidio': {
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Financial District': 23,
        'North Beach': 18
    }
}

# Meeting data: [dummy, Stephanie, William, Elizabeth, Joseph, Anthony, Barbara, Carol, Sandra, Kenneth]
names = [
    'dummy',
    'Stephanie',
    'William',
    'Elizabeth',
    'Joseph',
    'Anthony',
    'Barbara',
    'Carol',
    'Sandra',
    'Kenneth'
]
locations = [
    'Marina District',
    'Richmond District',
    'Union Square',
    'Nob Hill',
    'Fisherman\'s Wharf',
    'Golden Gate Park',
    'Embarcadero',
    'Financial District',
    'North Beach',
    'Presidio'
]
available_start = [0, 915, 645, 735, 765, 780, 1155, 705, 600, 1275]
available_end = [0, 1290, 1050, 900, 840, 1230, 1230, 975, 750, 1335]
min_durations = [0, 75, 45, 105, 75, 75, 75, 60, 15, 45]

# Create Z3 solver and variables
s = Optimize()
meet = []
start = []

# Dummy meeting (always true, start at 0)
meet.append(True)
start.append(0)

# Variables for real meetings
for i in range(1, 10):
    meet.append(Bool(f'meet_{i}'))
    start.append(Int(f'start_{i}'))

# Constraints for each meeting
for i in range(1, 10):
    s.add(Implies(meet[i], start[i] >= available_start[i]))
    s.add(Implies(meet[i], start[i] <= available_end[i] - min_durations[i]))

# Pairwise constraints for all meetings (including dummy)
for i in range(10):
    for j in range(i + 1, 10):
        time_ij = travel_dict[locations[i]][locations[j]]
        time_ji = travel_dict[locations[j]][locations[i]]
        # If both meetings occur, ensure travel time is respected
        if i == 0:  # Dummy meeting
            s.add(Implies(meet[j], start[i] + min_durations[i] + time_ij <= start[j]))
        else:
            s.add(Implies(And(meet[i], meet[j]),
                          Or(
                              start[i] + min_durations[i] + time_ij <= start[j],
                              start[j] + min_durations[j] + time_ji <= start[i]
                          )))

# Maximize the number of meetings
objective = Sum([If(meet[i], 1, 0) for i in range(1, 10)])
s.maximize(objective)

# Solve the problem
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    total_met = 0
    schedule = []
    for i in range(1, 10):
        if m.evaluate(meet[i]):
            total_met += 1
            start_time = m.evaluate(start[i])
            if isinstance(start_time, IntNumRef):
                start_val = start_time.as_long()
            else:
                start_val = start_time
            end_val = start_val + min_durations[i]
            schedule.append((names[i], locations[i], start_val, end_val))
    print(f"Total friends met: {total_met}")
    for name, loc, start_val, end_val in schedule:
        start_hour = start_val // 60
        start_minute = start_val % 60
        end_hour = end_val // 60
        end_minute = end_val % 60
        print(f"Meet {name} at {loc} from {start_hour:02d}:{start_minute:02d} to {end_hour:02d}:{end_minute:02d}")
else:
    print("No solution found")