from z3 import *

# Create a solver instance
solver = Solver()

# Define variables:
# "day" takes value 0 for Monday and 1 for Tuesday.
# "s" is the meeting start time in minutes after 9:00.
day = Int('day')
s = Int('s')

# Meeting duration is 60 minutes.
duration = 60

# s must be chosen so that s + duration <= 480 (i.e. finish by 17:00)
solver.add(s >= 0, s <= 480 - duration)

# day is either 0 (Monday) or 1 (Tuesday)
solver.add(Or(day == 0, day == 1))

# Define the blocked intervals for each day relative to 9:00.
# For example, 9:30 is 30 minutes after 9:00 and 10:00 is 60 minutes.
# Monday blocked slots

monday_blocks = [
    (30, 60),    # Gary: 9:30 to 10:00
    (120, 240),  # Gary: 11:00 to 13:00
    (300, 330),  # Gary: 14:00 to 14:30
    (450, 480),  # Gary: 16:30 to 17:00
    (0, 30),     # David: 9:00 to 9:30
    (60, 240),   # David: 10:00 to 13:00
    (330, 450)   # David: 14:30 to 16:30
]

# Tuesday blocked slots

tuesday_blocks = [
    (0, 30),     # Gary: 9:00 to 9:30
    (90, 120),   # Gary: 10:30 to 11:00
    (330, 420),  # Gary: 14:30 to 16:00
    (0, 30),     # David: 9:00 to 9:30
    (60, 90),    # David: 10:00 to 10:30
    (120, 210),  # David: 11:00 to 12:30
    (240, 330),  # David: 13:00 to 14:30
    (360, 420),  # David: 15:00 to 16:00
    (450, 480)   # David: 16:30 to 17:00
]

# For a meeting to avoid a blocked interval the meeting interval [s, s+duration]
# must either finish before a blocked interval starts OR start after it ends.
# We add these constraints conditionally: if day == 0 then the meeting must not intersect any Monday block,
# and if day == 1 then the meeting must not intersect any Tuesday block.

for (blk_start, blk_end) in monday_blocks:
    solver.add(Implies(day == 0, Or(s + duration <= blk_start, s >= blk_end)))

for (blk_start, blk_end) in tuesday_blocks:
    solver.add(Implies(day == 1, Or(s + duration <= blk_start, s >= blk_end)))

# Check if a solution exists and extract values.
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[s].as_long()
    
    # Convert meeting start time from minutes after 9:00 into HH:MM format.
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60
    
    meeting_end = meeting_start + duration
    end_hour = 9 + meeting_end // 60
    end_minute = meeting_end % 60
    
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    start_time_str = f"{start_hour:02d}:{start_minute:02d}"
    end_time_str = f"{end_hour:02d}:{end_minute:02d}"
    
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")