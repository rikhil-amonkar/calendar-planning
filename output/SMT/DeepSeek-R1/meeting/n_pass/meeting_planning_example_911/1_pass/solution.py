from z3 import *

# Define the travel time matrix (11x11) for locations 0 to 10
T = [
    [0, 20, 11, 22, 6, 16, 16, 21, 20, 19, 21],
    [23, 0, 22, 6, 18, 18, 7, 9, 17, 7, 8],
    [13, 23, 0, 25, 7, 7, 20, 16, 11, 22, 26],
    [25, 5, 25, 0, 21, 21, 10, 12, 20, 10, 5],
    [6, 19, 7, 20, 0, 10, 15, 17, 15, 19, 21],
    [16, 17, 9, 19, 10, 0, 17, 9, 7, 21, 22],
    [17, 8, 17, 9, 13, 14, 0, 11, 17, 7, 9],
    [22, 11, 18, 14, 16, 11, 12, 0, 10, 16, 17],
    [21, 18, 12, 20, 15, 7, 18, 11, 0, 22, 23],
    [17, 10, 22, 11, 18, 20, 9, 18, 24, 0, 9],
    [20, 7, 23, 4, 19, 21, 8, 15, 22, 9, 0]
]

# Meeting data: min_duration, avail_start, avail_end for meetings 0 to 10
# Index 0 is dummy (handled separately)
min_dur = [0, 15, 75, 105, 75, 30, 90, 120, 120, 60, 45]
avail_start = [0, 1050, 1020, 855, 615, 840, 495, 675, 900, 690, 795]
avail_end = [0, 1230, 1155, 960, 735, 1170, 765, 795, 1095, 1260, 915]

# Names of friends for each meeting index
names = [
    "Dummy (The Castro)",
    "Steven (North Beach)",
    "Sarah (Golden Gate Park)",
    "Brian (Embarcadero)",
    "Stephanie (Haight-Ashbury)",
    "Melissa (Richmond District)",
    "Nancy (Nob Hill)",
    "David (Marina District)",
    "James (Presidio)",
    "Elizabeth (Union Square)",
    "Robert (Financial District)"
]

# Create Z3 variables and solver
s = Optimize()
num_meetings = 11

# met[i] is True if we meet friend i
met = [Bool(f'met_{i}') for i in range(num_meetings)]
# start[i] and end[i] are the start and end times of meeting i
start = [Real(f'start_{i}') for i in range(num_meetings)]
end = [Real(f'end_{i}') for i in range(num_meetings)]

# Dummy meeting (index 0) is fixed at 9:00 AM (540 minutes)
s.add(met[0] == True)
s.add(start[0] == 540)
s.add(end[0] == 540)

# Constraints for meetings 1 to 10
for i in range(1, num_meetings):
    # If meeting i is met, it must start within availability window and meet minimum duration
    s.add(Implies(met[i], start[i] >= avail_start[i]))
    s.add(Implies(met[i], end[i] == start[i] + min_dur[i]))
    s.add(Implies(met[i], end[i] <= avail_end[i]))

# Disjunctive constraints for every pair of meetings (including dummy)
for i in range(num_meetings):
    for j in range(num_meetings):
        if i == j:
            continue
        # If both meetings are met, enforce travel time between them
        s.add(Implies(And(met[i], met[j]),
            Or(
                start[j] >= end[i] + T[i][j],
                start[i] >= end[j] + T[j][i]
            )
        ))

# Maximize the number of friends met (excluding dummy)
objective = Sum([If(met[i], 1, 0) for i in range(1, num_meetings)])
s.maximize(objective)

# Solve the problem
if s.check() == sat:
    model = s.model()
    # Count and list the meetings that are met
    met_count = 0
    schedule = []
    for i in range(1, num_meetings):
        if is_true(model[met[i]]):
            met_count += 1
            start_val = model[start[i]].as_fraction() if isinstance(model[start[i]], RatNumRef) else model[start[i]]
            end_val = model[end[i]].as_fraction() if isinstance(model[end[i]], RatNumRef) else model[end[i]]
            # Convert fractional values to float for time conversion
            start_min = float(start_val.numerator_as_long()) / float(start_val.denominator_as_long()) if isinstance(start_val, AlgebraicNumRef) else float(start_val)
            end_min = float(end_val.numerator_as_long()) / float(end_val.denominator_as_long()) if isinstance(end_val, AlgebraicNumRef) else float(end_val)
            # Convert minutes to time string
            start_hour = int(start_min) // 60
            start_minute = int(start_min) % 60
            end_hour = int(end_min) // 60
            end_minute = int(end_min) % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            schedule.append((names[i], start_str, end_str))
    # Output the solution
    print(f"SOLUTION: Met {met_count} friends")
    for name, s_time, e_time in schedule:
        print(f"Meet {name} from {s_time} to {e_time}")
else:
    print("SOLUTION: No feasible schedule found")