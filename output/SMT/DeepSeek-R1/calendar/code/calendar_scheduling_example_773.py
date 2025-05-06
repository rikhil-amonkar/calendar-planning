from z3 import Solver, Int, Or, And, Implies, sat

s = Solver()
day = Int('day')
start = Int('start')

total_time = day * 480 + start  # Total minutes since Monday 9:00

# Valid days: Monday (0), Tuesday (1), Wednesday (2)
s.add(day >= 0, day <= 2)
s.add(start >= 0, start <= 420)  # 1hr meeting within 9:00-17:00

# Roy's schedule constraints for each day
# Monday constraints
monday_busy = [(60, 150), (180, 240), (300, 330), (360, 480)]
monday_constraints = [Or(start + 60 <= s_start, start >= s_end) for s_start, s_end in monday_busy]
s.add(Implies(day == 0, And(monday_constraints)))

# Tuesday constraints
tuesday_busy = [(90, 150), (180, 330), (360, 390), (420, 480)]
tuesday_constraints = [Or(start + 60 <= s_start, start >= s_end) for s_start, s_end in tuesday_busy]
s.add(Implies(day == 1, And(tuesday_constraints)))

# Wednesday constraints
wednesday_busy = [(30, 150), (210, 300), (330, 390), (450, 480)]
wednesday_constraints = [Or(start + 60 <= s_start, start >= s_end) for s_start, s_end in wednesday_busy]
s.add(Implies(day == 2, And(wednesday_constraints)))

# Patrick has no constraints

# Find earliest possible time
s.minimize(total_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    day_names = ["Monday", "Tuesday", "Wednesday"]
    hours = st // 60 + 9
    minutes = st % 60
    print(f"Meeting starts on {day_names[d]} at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")