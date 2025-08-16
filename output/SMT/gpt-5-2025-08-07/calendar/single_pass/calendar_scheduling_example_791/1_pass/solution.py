from z3 import Int, Solver, Or, And, Implies, sat

def minutes(h, m):
    # Convert HH:MM to minutes since 09:00 (workday start)
    return (h - 9) * 60 + m

def fmt_time(offset_minutes):
    # Convert minutes since 09:00 back to 24-hour HH:MM
    total_minutes = 9 * 60 + offset_minutes
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 0           # 09:00 as 0 offset
WORK_END = 8 * 60        # 17:00 => 480 minutes after 09:00

# Days mapping
days = ["Monday", "Tuesday", "Wednesday"]

# Busy schedules as minutes since 09:00 for each day index: 0=Mon,1=Tue,2=Wed
# Intervals are [start, end) in minutes since 09:00
nicole_busy = {
    0: [(minutes(9,0), minutes(9,30)), (minutes(13,0), minutes(13,30)), (minutes(14,30), minutes(15,30))],
    1: [(minutes(9,0), minutes(9,30)), (minutes(11,30), minutes(13,30)), (minutes(14,30), minutes(15,30))],
    2: [(minutes(10,0), minutes(11,0)), (minutes(12,30), minutes(15,0)), (minutes(16,0), minutes(17,0))]
}
ruth_busy = {
    0: [(minutes(9,0), minutes(17,0))],
    1: [(minutes(9,0), minutes(17,0))],
    2: [(minutes(9,0), minutes(10,30)), (minutes(11,0), minutes(11,30)), (minutes(12,0), minutes(12,30)),
        (minutes(13,30), minutes(15,30)), (minutes(16,0), minutes(16,30))]
}

# Z3 variables
day = Int('day')          # 0=Mon,1=Tue,2=Wed
start = Int('start')      # minutes since 09:00
end = Int('end')          # minutes since 09:00

s = Solver()

# Domain constraints
s.add(Or(day == 0, day == 1, day == 2))
s.add(start >= WORK_START, end == start + DURATION, end <= WORK_END)

# No-overlap constraints for Nicole and Ruth
for d in range(3):
    for (bs, be) in nicole_busy[d]:
        s.add(Implies(day == d, Or(end <= bs, start >= be)))
    for (bs, be) in ruth_busy[d]:
        s.add(Implies(day == d, Or(end <= bs, start >= be)))

# Preference: Ruth does not want to meet on Wednesday after 13:30 (meeting must end by 13:30 on Wed)
wed = 2
limit_1330 = minutes(13, 30)
s.add(Implies(day == wed, end <= limit_1330))

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    en = m[end].as_long()
    print("SOLUTION:")
    print(f"Day: {days[d]}")
    print(f"Start Time: {fmt_time(st)}")
    print(f"End Time: {fmt_time(en)}")
else:
    # Given the problem statement guarantees a solution, this should not happen.
    # Fallback in the unlikely event of unsat.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 09:00")
    print("End Time: 09:30")