from z3 import *

# Helper to convert HH:MM to minutes since midnight
def mm(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Busy schedules as [start_minute, end_minute) intervals
natalie_busy = {
    0: [(mm("09:00"), mm("09:30")),
        (mm("10:00"), mm("12:00")),
        (mm("12:30"), mm("13:00")),
        (mm("14:00"), mm("14:30")),
        (mm("15:00"), mm("16:30"))],
    1: [(mm("09:00"), mm("09:30")),
        (mm("10:00"), mm("10:30")),
        (mm("12:30"), mm("14:00")),
        (mm("16:00"), mm("17:00"))],
    2: [(mm("11:00"), mm("11:30")),
        (mm("16:00"), mm("16:30"))],
    3: [(mm("10:00"), mm("11:00")),
        (mm("11:30"), mm("15:00")),
        (mm("15:30"), mm("16:00")),
        (mm("16:30"), mm("17:00"))],
}

william_busy = {
    0: [(mm("09:30"), mm("11:00")),
        (mm("11:30"), mm("17:00"))],
    1: [(mm("09:00"), mm("13:00")),
        (mm("13:30"), mm("16:00"))],
    2: [(mm("09:00"), mm("12:30")),
        (mm("13:00"), mm("14:30")),
        (mm("15:30"), mm("16:00")),
        (mm("16:30"), mm("17:00"))],
    3: [(mm("09:00"), mm("10:30")),
        (mm("11:00"), mm("11:30")),
        (mm("12:00"), mm("12:30")),
        (mm("13:00"), mm("14:00")),
        (mm("15:00"), mm("17:00"))],
}

# Z3 variables
day = Int('day')         # 0=Mon, 1=Tue, 2=Wed, 3=Thu
start = Int('start')     # minutes since midnight
end = Int('end')

s = Solver()

# Meeting duration 60 minutes, within work hours 09:00 to 17:00
s.add(day >= 0, day <= 3)
s.add(end == start + 60)
s.add(start >= mm("09:00"))
s.add(end <= mm("17:00"))

# Optional: align to 30-minute boundaries for neat times
s.add(start % 30 == 0)

# No overlap with busy schedules on the chosen day
def no_overlap_on_day(chosen_day, busy_intervals):
    if not busy_intervals:
        return True
    return And([Or(end <= s_i, start >= e_i) for (s_i, e_i) in busy_intervals])

for d in range(4):
    s.add(Implies(day == d, no_overlap_on_day(d, natalie_busy[d])))
    s.add(Implies(day == d, no_overlap_on_day(d, william_busy[d])))

if s.check() == sat:
    m = s.model()
    d_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = m[end].as_long()
    def fmt(t):
        return f"{t//60:02d}:{t%60:02d}"
    print("SOLUTION:")
    print(f"Day: {days[d_val]}")
    print(f"Start Time: {fmt(start_val)}")
    print(f"End Time: {fmt(end_val)}")
else:
    # Given the problem guarantees a solution, this should not happen.
    # Included for completeness.
    print("SOLUTION:")
    print("Day: N/A")
    print("Start Time: 00:00")
    print("End Time: 00:00")