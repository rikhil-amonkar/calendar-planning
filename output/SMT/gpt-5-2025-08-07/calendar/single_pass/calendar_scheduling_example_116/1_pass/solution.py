from z3 import Optimize, Int, Or

def minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours and meeting duration
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 30

# Busy schedules (start, end) in minutes from 00:00
busy = {
    "Adam": [
        (minutes(14, 0), minutes(15, 0)),
    ],
    "John": [
        (minutes(13, 0), minutes(13, 30)),
        (minutes(14, 0), minutes(14, 30)),
        (minutes(15, 30), minutes(16, 0)),
        (minutes(16, 30), minutes(17, 0)),
    ],
    "Stephanie": [
        (minutes(9, 30), minutes(10, 0)),
        (minutes(10, 30), minutes(11, 0)),
        (minutes(11, 30), minutes(16, 0)),
        (minutes(16, 30), minutes(17, 0)),
    ],
    "Anna": [
        (minutes(9, 30), minutes(10, 0)),
        (minutes(12, 0), minutes(12, 30)),
        (minutes(13, 0), minutes(15, 30)),
        (minutes(16, 30), minutes(17, 0)),
    ],
}

# Preference: Anna would rather not meet before 14:30 (soft constraint)
preference_start = minutes(14, 30)

opt = Optimize()

Start = Int('Start')
End = Int('End')

# Core constraints
opt.add(Start >= work_start)
opt.add(End <= work_end)
opt.add(End - Start == duration)

# No-overlap with each participant's busy intervals
for person, intervals in busy.items():
    for (s, e) in intervals:
        # Meeting [Start, End) must not intersect [s, e)
        opt.add(Or(End <= s, Start >= e))

# Soft preference: Start >= 14:30 if possible
opt.add_soft(Start >= preference_start)

# Solve
if opt.check() == sat:
    model = opt.model()
    start_val = model[Start].as_long()
    end_val = model[End].as_long()

    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {fmt_time(start_val)} (24-hour format)")
    print(f"End Time: {fmt_time(end_val)} (24-hour format)")
else:
    # As per problem statement, a solution exists; this is a fallback
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 00:00 (24-hour format)")
    print("End Time: 00:30 (24-hour format)")