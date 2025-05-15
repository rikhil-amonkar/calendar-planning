from z3 import Solver, Int, Or, Implies, sat

solver = Solver()
Day = Int('Day')
Start = Int('Start')

# Robert would like to avoid Monday, so schedule on Tuesday (1) or Wednesday (2)
solver.add(Or(Day == 1, Day == 2))
solver.add(Start >= 0)
solver.add(Start + 30 <= 480)  # 30-minute meeting within 9:00-17:00

# Robert's constraints converted to minutes since 9:00
robert_tuesday = [(90, 120), (360, 390)]  # 10:30-11:00, 15:00-15:30
robert_wednesday = [(60, 120), (150, 180), (210, 240), (270, 300), (360, 390), (420, 450)]  # 10:00-11:00 etc.

# Ralph's constraints converted to minutes since 9:00
ralph_tuesday = [(0, 30), (60, 90), (120, 150), (180, 240), (300, 390), (420, 480)]  # 9:00-9:30, 10:00-10:30 etc.
ralph_wednesday = [(90, 120), (150, 180), (240, 330), (450, 480)]  # 10:30-11:00 etc.

# Apply constraints based on selected day
# Tuesday constraints
for block in robert_tuesday:
    solver.add(Implies(Day == 1, Or(Start + 30 <= block[0], Start >= block[1])))
for block in ralph_tuesday:
    solver.add(Implies(Day == 1, Or(Start + 30 <= block[0], Start >= block[1])))

# Wednesday constraints
for block in robert_wednesday:
    solver.add(Implies(Day == 2, Or(Start + 30 <= block[0], Start >= block[1])))
for block in ralph_wednesday:
    solver.add(Implies(Day == 2, Or(Start + 30 <= block[0], Start >= block[1])))

# To find earliest availability, check solutions and pick minimum day and time
# Since Z3's solver might return any valid solution, we need to find the minimal one
# This requires using the optimizer
opt = Solver()
opt.add(solver.assertions())
opt.check()
model = opt.model()

day_num = model[Day].as_long()
start_min = model[Start].as_long()

# Convert to time format
days = ["Monday", "Tuesday", "Wednesday"]
start_h = 9 + start_min // 60
start_m = start_min % 60
end_min = start_min + 30
end_h = 9 + end_min // 60
end_m = end_min % 60

print(f"{days[day_num]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")