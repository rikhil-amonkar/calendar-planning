from z3 import *

# Create the solver instance
s = Solver()

# Define variables
# day: 0 means Monday, 1 means Tuesday
# start: meeting start time in minutes after midnight (using 24h clock)
day = Int('day')
start = Int('start')
duration = 30
end = start + duration

# Working hours (in minutes): 9:00 = 540, 17:00 = 1020
work_start = 540
work_end = 1020

# The meeting must lie fully in the working hours.
s.add(start >= work_start, end <= work_end)

# day must be either Monday (0) or Tuesday (1)
s.add(Or(day == 0, day == 1))

# Jeffrey is free all week, so no constraints from his side.

# Harold's busy times and preferences:
# ----- For Monday (day==0) -----
# Harold is busy on Monday from 9:00 to 10:00 and from 10:30 to 17:00.
# The only available free slot on Monday is from 10:00 (600) to 10:30 (630).
# Thus, if the meeting is on Monday, we require: start == 600.
monday_slot = start == 600
s.add(Implies(day == 0, monday_slot))

# ----- For Tuesday (day==1) -----
# Harold is busy on Tuesday during:
#   9:00-9:30  -> 540-570
#   10:30-11:30-> 630-690
#   12:30-13:30-> 750-810
#   14:30-15:30-> 870-930
#   16:00-17:00-> 960-1020
# His additional preference is to avoid any Tuesday meetings that start before 14:30 (870).
# Considering the busy times, the only free interval on Tuesday after 14:30 is from 15:30 (930) to 16:00 (960).
# So if the meeting is on Tuesday, we require: start == 930.
tuesday_slot = start == 930
s.add(Implies(day == 1, tuesday_slot))

# Harold prefers to avoid Monday, so whenever a Tuesday solution is available, choose Tuesday.
# To enforce the preference, we add a hard constraint that the meeting is on Tuesday.
s.add(day == 1)

# Check and print the solution
if s.check() == sat:
    m = s.model()
    sol_day = m[day].as_long()  # 0 means Monday, 1 means Tuesday
    sol_start = m[start].as_long()
    sol_end = sol_start + duration

    # Map numeric day to day string
    day_str = "Monday" if sol_day == 0 else "Tuesday"

    # Helper function to convert minutes to HH:MM format.
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day:", day_str)
    print("Start Time:", minutes_to_time(sol_start))
    print("End Time:", minutes_to_time(sol_end))
else:
    print("No solution found.")