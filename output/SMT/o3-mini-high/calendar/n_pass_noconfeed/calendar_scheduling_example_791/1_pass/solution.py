from z3 import *

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Initialize the solver
s = Solver()

# Define variables:
# day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
day = Int("day")
# meeting start time in minutes (since midnight)
m_start = Int("m_start")
m_end = m_start + 30  # meeting duration is 30 minutes

# Meeting must be within work hours: between 9:00 (540) and 17:00 (1020)
s.add(m_start >= 540)
s.add(m_end <= 1020)
# The day must be one of: Monday (0), Tuesday (1), or Wednesday (2)
s.add(Or(day == 0, day == 1, day == 2))

# For each participant and each day, add constraints that the meeting does not overlap any busy interval.
# A meeting [m_start, m_start+30] does not overlap a busy interval [b_start, b_end]
# if: m_end <= b_start  OR  m_start >= b_end

# Monday constraints (day == 0)
# Nicole is busy on Monday at: 9:00–9:30, 13:00–13:30, 14:30–15:30.
mon_nicole_busy = [(540, 570), (780, 810), (870, 930)]
for (b_start, b_end) in mon_nicole_busy:
    s.add(Implies(day == 0, Or(m_end <= b_start, m_start >= b_end)))
# Ruth is busy all day Monday: 9:00–17:00.
s.add(Implies(day == 0, Or(m_end <= 540, m_start >= 1020)))

# Tuesday constraints (day == 1)
# Nicole is busy on Tuesday at: 9:00–9:30, 11:30–13:30, 14:30–15:30.
tue_nicole_busy = [(540, 570), (690, 810), (870, 930)]
for (b_start, b_end) in tue_nicole_busy:
    s.add(Implies(day == 1, Or(m_end <= b_start, m_start >= b_end)))
# Ruth is busy all day Tuesday: 9:00–17:00.
s.add(Implies(day == 1, Or(m_end <= 540, m_start >= 1020)))

# Wednesday constraints (day == 2)
# Nicole is busy on Wednesday at: 10:00–11:00, 12:30–15:00, 16:00–17:00.
wed_nicole_busy = [(600, 660), (750, 900), (960, 1020)]
for (b_start, b_end) in wed_nicole_busy:
    s.add(Implies(day == 2, Or(m_end <= b_start, m_start >= b_end)))
# Ruth is busy on Wednesday at: 9:00–10:30, 11:00–11:30, 12:00–12:30, 13:30–15:30, 16:00–16:30.
wed_ruth_busy = [(540, 630), (660, 690), (720, 750), (810, 930), (960, 990)]
for (b_start, b_end) in wed_ruth_busy:
    s.add(Implies(day == 2, Or(m_end <= b_start, m_start >= b_end)))
# Additionally, Ruth does not want to meet on Wednesday after 13:30.
# That is, on Wednesday the meeting must finish by 13:30 (810 minutes), so m_start <= 780.
s.add(Implies(day == 2, m_start <= 780))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    chosen_day = m[day].as_long()
    meeting_start_val = m[m_start].as_long()
    meeting_end_val = meeting_start_val + 30
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    # Print the result in the format HH:MM:HH:MM along with the day of the week.
    print(f"{day_names[chosen_day]} {minutes_to_time(meeting_start_val)}:{minutes_to_time(meeting_end_val)}")
else:
    print("No meeting time found.")