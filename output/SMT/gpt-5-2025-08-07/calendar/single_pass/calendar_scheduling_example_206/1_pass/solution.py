from z3 import Int, Solver, Or, And, sat

def to_slot(time_str):
    h, m = map(int, time_str.split(':'))
    return ((h - 9) * 60 + m) // 30  # 30-minute slots from 09:00

def slot_to_time(slot):
    minutes_from_9 = slot * 30
    hour = 9 + minutes_from_9 // 60
    minute = minutes_from_9 % 60
    return f"{hour:02d}:{minute:02d}"

# Busy schedules (half-open intervals [start, end))
Shirley = [("10:30","11:00"),("12:00","12:30")]
Jacob   = [("09:00","09:30"),("10:00","10:30"),("11:00","11:30"),("12:30","13:30"),("14:30","15:00")]
Stephen = [("11:30","12:00"),("12:30","13:00")]
Margaret= [("09:00","09:30"),("10:30","12:30"),("13:00","13:30"),("15:00","15:30"),("16:30","17:00")]
Mason   = [("09:00","10:00"),("10:30","11:00"),("11:30","12:30"),("13:00","13:30"),("14:00","14:30"),("16:30","17:00")]

participants = [Shirley, Jacob, Stephen, Margaret, Mason]

# Z3 variable: meeting start slot (0 = 09:00, ..., 15 = 16:30)
s = Int('s')
solver = Solver()

# Meeting within work hours and half-hour duration
solver.add(And(s >= 0, s <= 15))  # start between 09:00 and 16:30 inclusive

# No overlap with any participant's busy intervals
for person in participants:
    for start_str, end_str in person:
        start_slot = to_slot(start_str)
        end_slot = to_slot(end_str)  # half-open
        # enforce s not in [start_slot, end_slot)
        solver.add(Or(s < start_slot, s >= end_slot))

# Preference: Margaret does not want to meet before 14:30 on Monday
solver.add(s >= to_slot("14:30"))

if solver.check() == sat:
    m = solver.model()
    start_slot = m[s].as_long()
    end_slot = start_slot + 1  # 30 minutes later
    start_time = slot_to_time(start_slot)
    end_time = slot_to_time(end_slot)
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    # Problem statement guarantees a solution exists; this is a fallback.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 00:00")
    print("End Time: 00:30")