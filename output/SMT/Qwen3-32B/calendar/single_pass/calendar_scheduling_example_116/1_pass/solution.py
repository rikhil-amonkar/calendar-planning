import z3

solver = z3.Solver()

s = z3.Int('s')

# Define the overall time constraints (9:00 AM to 5:00 PM in minutes since midnight)
solver.add(s >= 540, s <= 990)  # 9:00 is 540, 17:00 is 1020, meeting is 30 min so s <= 990

# Adam's busy time: 14:00-15:00 (840-900)
solver.add(z3.Or(s + 30 <= 840, s >= 900))

# John's busy times
john_buses = [(780, 810), (840, 870), (930, 960), (990, 1020)]
for start, end in john_buses:
    solver.add(z3.Or(s + 30 <= start, s >= end))

# Stephanie's busy times
steph_buses = [(570, 600), (630, 660), (690, 960), (990, 1020)]
for start, end in steph_buses:
    solver.add(z3.Or(s + 30 <= start, s >= end))

# Anna's busy times
anna_buses = [(570, 600), (720, 750), (780, 930), (990, 1020)]
for start, end in anna_buses:
    solver.add(z3.Or(s + 30 <= start, s >= end))

# Anna's preference: start time >= 14:30 (870 minutes)
solver.add(s >= 870)

if solver.check() == z3.sat:
    model = solver.model()
    start_min = model[s].as_long()
    # Convert start time to HH:MM format
    start_hours = start_min // 60
    start_minutes = start_min % 60
    start_time = f"{start_hours:02d}:{start_minutes:02d}"
    # End time is start + 30 minutes
    end_min = start_min + 30
    end_hours = end_min // 60
    end_minutes = end_min % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")