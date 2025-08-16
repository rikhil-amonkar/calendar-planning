from z3 import Solver, Int, Or, Implies

# Create the solver
solver = Solver()

# Define variables:
# day: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
# start_time is measured in minutes from midnight.
day = Int("day")
start_time = Int("start_time")
duration = 60  # duration is 60 minutes

# Working hours constraints: meeting must start no earlier than 9:00 (540 minutes)
# and must end by 17:00 (1020 minutes).
solver.add(start_time >= 540, start_time + duration <= 1020)
solver.add(Or(day == 0, day == 1, day == 2, day == 3, day == 4))

# Define the busy intervals (in minutes) for each day. 
# Each interval is a tuple (busy_start, busy_end) meaning that the participant is busy 
# from busy_start (inclusive) to busy_end (exclusive).
# Monday (day = 0)
#   Diane: 12:00-12:30  => (720,750), 15:00-15:30 => (900,930)
#   Matthew: 9:00-10:00  => (540,600), 10:30-17:00 => (630,1020)
busy = {
    0: [(540, 600), (630, 1020), (720, 750), (900, 930)],
    # Tuesday (day = 1)
    #   Diane: 10:00-11:00 => (600,660), 11:30-12:00 => (690,720),
    #           12:30-13:00 => (750,780), 16:00-17:00 => (960,1020)
    #   Matthew: 9:00-17:00 => (540,1020)
    1: [(540, 1020), (600, 660), (690, 720), (750, 780), (960, 1020)],
    # Wednesday (day = 2)
    #   Diane: 9:00-9:30 => (540,570), 14:30-15:00 => (870,900), 16:30-17:00 => (990,1020)
    #   Matthew: 9:00-11:00 => (540,660), 12:00-14:30 => (720,870), 16:00-17:00 => (960,1020)
    2: [(540, 660), (720, 870), (960, 1020), (540, 570), (870, 900), (990, 1020)],
    # Thursday (day = 3)
    #   Diane: 15:30-16:30 => (930,990)
    #   Matthew: 9:00-16:00 => (540,960)
    3: [(540, 960), (930, 990)],
    # Friday (day = 4)
    #   Diane: 9:30-11:30 => (570,690), 14:30-15:00 => (870,900), 16:00-17:00 => (960,1020)
    #   Matthew: 9:00-17:00 => (540,1020)
    4: [(540, 1020), (570, 690), (870, 900), (960, 1020)]
}

# For each busy interval on a given day, ensure that our one-hour meeting does not overlap it.
# Two intervals [s, s+duration] and [b_start, b_end] do not overlap if either:
#    meeting ends on or before the busy interval starts, OR
#    meeting starts on or after the busy interval ends.
for d in busy:
    for (b_start, b_end) in busy[d]:
        solver.add( Implies(day == d, Or(start_time + duration <= b_start, start_time >= b_end)) )

# Additional preference: Matthew would rather not meet on Wednesday before 12:30.
# Wednesday is day 2 and 12:30 is 750 minutes.
solver.add(Implies(day == 2, start_time >= 750))

# Check for a solution and print it in the required format.
if solver.check() == 'sat':
    model = solver.model()
    sol_day = model[day].as_long()
    sol_start = model[start_time].as_long()
    sol_end = sol_start + duration

    # Map day numbers to day names.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    day_str = day_names[sol_day]

    # Helper function to convert minutes to HH:MM format.
    def minutes_to_hhmm(m):
        hrs = m // 60
        mins = m % 60
        return f"{hrs:02d}:{mins:02d}"

    print("SOLUTION:")
    print("Day: " + day_str)
    print("Start Time: " + minutes_to_hhmm(sol_start))
    print("End Time: " + minutes_to_hhmm(sol_end))
else:
    print("No solution found.")