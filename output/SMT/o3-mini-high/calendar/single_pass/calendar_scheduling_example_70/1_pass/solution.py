from z3 import *

# Create an Optimize() solver to minimize the meeting start time (earliest meeting)
solver = Optimize()

# Define the meeting start time variable in minutes from midnight.
meeting_start = Int('meeting_start')
duration = 30
meeting_end = meeting_start + duration

# Work hours: 9:00 to 17:00 -> 9:00 = 540 minutes, 17:00 = 1020 minutes.
solver.add(meeting_start >= 540)        # Meeting cannot start before 9:00.
solver.add(meeting_end <= 1020)           # Meeting must finish by 17:00.

# Denise's busy intervals:
# Block 1: 12:00 to 12:30  -> [720, 750]
solver.add(Or(meeting_end <= 720, meeting_start >= 750))
# Block 2: 15:30 to 16:00  -> [930, 960]
solver.add(Or(meeting_end <= 930, meeting_start >= 960))

# Angela has no busy intervals, so no additional constraints.

# Natalie's busy intervals:
# Block 1: 9:00 to 11:30   -> [540, 690]
# To avoid overlap, the meeting must start at or after 11:30.
solver.add(meeting_start >= 690)
# Block 2: 12:00 to 13:00  -> [720, 780]
solver.add(Or(meeting_end <= 720, meeting_start >= 780))
# Block 3: 14:00 to 14:30  -> [840, 870]
solver.add(Or(meeting_end <= 840, meeting_start >= 870))
# Block 4: 15:00 to 17:00  -> [900, 1020]
# Since meeting cannot be pushed later (working hours), we require meeting_end <= 900.
solver.add(meeting_end <= 900)

# Optimize for the earliest meeting by minimizing meeting_start.
solver.minimize(meeting_start)

if solver.check() == sat:
    model = solver.model()
    start = model[meeting_start].as_long()
    end = start + duration
    
    # Convert minutes from midnight into HH:MM format.
    start_hour = start // 60
    start_min = start % 60
    end_hour = end // 60
    end_min = end % 60
    start_str = f"{start_hour:02d}:{start_min:02d}"
    end_str = f"{end_hour:02d}:{end_min:02d}"
    
    # Output the solution
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found.")