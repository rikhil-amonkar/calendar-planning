from z3 import *

# Define the variables
arrive_north_beach = Int('arrive_north_beach')
leave_north_beach = Int('leave_north_beach')
travel_to_union_square = Int('travel_to_union_square')
travel_to_russian_hill = Int('travel_to_russian_hill')
meet_emily = Int('meet_emily')
meet_margaret = Int('meet_margaret')
meet_both = Int('meet_both')

# Define the distances in minutes
distances = {
    'North Beach to Union Square': 7,
    'North Beach to Russian Hill': 4,
    'Union Square to North Beach': 10,
    'Union Square to Russian Hill': 13,
    'Russian Hill to North Beach': 5,
    'Russian Hill to Union Square': 11
}

# Define the constraints
s = Optimize()

# You arrive at North Beach at 9:00AM
s.add(arrive_north_beach == 9 * 60)

# You want to meet Emily for a minimum of 45 minutes
s.add(4 * 60 + 15 <= meet_emily)
s.add(meet_emily <= 5 * 60 + 15)

# You want to meet Margaret for a minimum of 120 minutes
s.add(7 * 60 + 0 <= meet_margaret)
s.add(meet_margaret <= 9 * 60 + 0)

# You can travel to Union Square from North Beach
s.add(leave_north_beach + distances['North Beach to Union Square'] <= meet_emily)

# You can travel to Russian Hill from North Beach
s.add(leave_north_beach + distances['North Beach to Russian Hill'] <= meet_margaret)

# You can travel to North Beach from Union Square
s.add(meet_emily + distances['Union Square to North Beach'] <= leave_north_beach)

# You can travel to North Beach from Russian Hill
s.add(meet_margaret + distances['Russian Hill to North Beach'] <= leave_north_beach)

# You can travel to Russian Hill from Union Square
s.add(meet_emily + distances['Union Square to Russian Hill'] <= leave_north_beach)

# You can travel to Union Square from Russian Hill
s.add(meet_margaret + distances['Russian Hill to Union Square'] <= leave_north_beach)

# You must meet with exactly 2 people
s.add(BoolVal(False) | (meet_emily > 0) == meet_margaret > 0)
s.add(BoolVal(False) | (meet_emily > 0) == meet_emily == 0)
s.add(BoolVal(False) | (meet_margaret > 0) == meet_margaret == 0)
s.add(meet_emily + meet_margaret == meet_both)

# Objective: minimize the total travel time
s.minimize(leave_north_beach - arrive_north_beach)

# Solve the problem
result = s.check()
if result == sat:
    model = s.model()
    print("Best schedule:")
    print(f"Arrive at North Beach: {model[arrive_north_beach] / 60} hours")
    print(f"Leave North Beach: {model[leave_north_beach] / 60} hours")
    print(f"Meet Emily: {model[meet_emily] / 60} hours")
    print(f"Meet Margaret: {model[meet_margaret] / 60} hours")
    print(f"Meet Both: {model[meet_both] / 60} hours")
else:
    print("No solution found.")