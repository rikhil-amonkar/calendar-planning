from z3 import *

# Create solver
s = Solver()

# Number of days
n_days = 25

# Activity definitions: 0=A, 1=B, 2=C
activities = [Int('act_%d' % i) for i in range(n_days)]

# Each day must have one of the three activities
for i in range(n_days):
    s.add(Or(activities[i] == 0, activities[i] == 1, activities[i] == 2))

# No consecutive same activities
for i in range(n_days - 1):
    s.add(activities[i] != activities[i+1])

# Count activities
countA = Sum([If(activities[i] == 0, 1, 0) for i in range(n_days)])
countB = Sum([If(activities[i] == 1, 1, 0) for i in range(n_days)])
countC = Sum([If(activities[i] == 2, 1, 0) for i in range(n_days)])

# Apply minimum requirements
s.add(countA >= 10)
s.add(countB >= 8)
s.add(countC >= 5)

# Solve and print the schedule
if s.check() == sat:
    m = s.model()
    schedule = [m[activities[i]] for i in range(n_days)]
    
    # Map numbers to activity names
    activity_names = {0: 'A', 1: 'B', 2: 'C'}
    for day in range(n_days):
        print(f"Day {day+1}: Activity {activity_names[schedule[day].as_long()]}")
else:
    print("No valid schedule found")