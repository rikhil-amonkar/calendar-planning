import z3

# Initialize Z3 solver
solver = z3.Solver()

# Define the start time as an integer in minutes since midnight
start_time = z3.Int('start_time')

# Work hours constraint: 9:00 AM (540) to 5:00 PM (1020)
# Meeting duration is 30 minutes
solver.add(start_time >= 540)
solver.add(start_time + 30 <= 1020)

# Frank's constraint: do not start after 9:30 AM (570 minutes)
solver.add(start_time <= 570)

# Emily's blocked times (in minutes)
emily_blocked = [
    (600, 630),  # 10:00 - 10:30
    (690, 750),  # 11:30 - 12:30
    (840, 900),  # 14:00 - 15:00
    (960, 990),  # 16:00 - 16:30
]

# Melissa's blocked times
melissa_blocked = [
    (570, 600),  # 9:30 - 10:00
    (870, 900),  # 14:30 - 15:00
]

# Frank's blocked times
frank_blocked = [
    (600, 630),   # 10:00 - 10:30
    (660, 690),   # 11:00 - 11:30
    (750, 780),   # 12:30 - 13:00
    (810, 870),   # 13:30 - 14:30
    (900, 960),   # 15:00 - 16:00
    (990, 1020),  # 16:30 - 17:00
]

# Add non-overlapping constraints for each blocked interval
def add_non_overlap_constraints(participant_blocked):
    for b_start, b_end in participant_blocked:
        solver.add(z3.Or(start_time >= b_end, start_time + 30 <= b_start))

add_non_overlap_constraints(emily_blocked)
add_non_overlap_constraints(melissa_blocked)
add_non_overlap_constraints(frank_blocked)

# Solve
if solver.check() == z3.sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30

    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time_str(start)}")
    print(f"End Time: {to_time_str(end)}")
else:
    print("No solution found.")