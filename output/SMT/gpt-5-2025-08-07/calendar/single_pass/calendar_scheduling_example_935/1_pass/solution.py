from z3 import *

def minutes(hh, mm):
    return (hh - 9) * 60 + mm  # minutes from 09:00

# Meeting parameters
duration = 30  # minutes
work_start = 0
work_end = 8 * 60  # 480 minutes (09:00 to 17:00)

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Busy schedules relative to 09:00 for each day index 0..4
# Each entry: list of (start_minute, end_minute) busy intervals [start, end)
terry_busy = {
    0: [(minutes(10,30), minutes(11,0)), (minutes(12,30), minutes(14,0)), (minutes(15,0), minutes(17,0))],
    1: [(minutes(9,30), minutes(10,0)), (minutes(10,30), minutes(11,0)), (minutes(14,0), minutes(14,30)), (minutes(16,0), minutes(16,30))],
    2: [(minutes(9,30), minutes(10,30)), (minutes(11,0), minutes(12,0)), (minutes(13,0), minutes(13,30)), (minutes(15,0), minutes(16,0)), (minutes(16,30), minutes(17,0))],
    3: [(minutes(9,30), minutes(10,0)), (minutes(12,0), minutes(12,30)), (minutes(13,0), minutes(14,30)), (minutes(16,0), minutes(16,30))],
    4: [(minutes(9,0), minutes(11,30)), (minutes(12,0), minutes(12,30)), (minutes(13,30), minutes(16,0)), (minutes(16,30), minutes(17,0))],
}

frances_busy = {
    0: [(minutes(9,30), minutes(11,0)), (minutes(11,30), minutes(13,0)), (minutes(14,0), minutes(14,30)), (minutes(15,0), minutes(16,0))],
    1: [(minutes(9,0), minutes(9,30)), (minutes(10,0), minutes(10,30)), (minutes(11,0), minutes(12,0)), (minutes(13,0), minutes(14,30)), (minutes(15,30), minutes(16,30))],
    2: [(minutes(9,30), minutes(10,0)), (minutes(10,30), minutes(11,0)), (minutes(11,30), minutes(16,0)), (minutes(16,30), minutes(17,0))],
    3: [(minutes(11,0), minutes(12,30)), (minutes(14,30), minutes(17,0))],
    4: [(minutes(9,30), minutes(10,30)), (minutes(11,0), minutes(12,30)), (minutes(13,0), minutes(16,0)), (minutes(16,30), minutes(17,0))],
}

# Z3 variables
day = Int('day')      # 0..4 (Mon..Fri)
start = Int('start')  # minutes from 09:00

end = start + duration

opt = Optimize()
opt.set(priority='lex')

# Domain constraints
opt.add(day >= 0, day <= 4)
opt.add(start >= work_start)
opt.add(end <= work_end)

# Optional: align to 30-minute blocks (common scheduling practice)
opt.add(start % 30 == 0)

# No overlap with busy times for the selected day
for d in range(5):
    for bs, be in terry_busy[d]:
        opt.add(Implies(day == d, Or(end <= bs, start >= be)))
    for bs, be in frances_busy[d]:
        opt.add(Implies(day == d, Or(end <= bs, start >= be)))

# Preferences:
# 1) Earliest availability overall
time_index = day * work_end + start  # minutes from Monday 09:00
opt.minimize(time_index)

# 2) Avoid Tuesday if possible (secondary objective)
is_tuesday = If(day == 1, 1, 0)
opt.minimize(is_tuesday)

if opt.check() != sat:
    raise RuntimeError("No feasible schedule found, but the problem statement guarantees one.")

m = opt.model()
day_val = m[day].as_long()
start_val = m[start].as_long()
end_val = start_val + duration

def to_hhmm(minutes_from_9):
    hh = 9 + minutes_from_9 // 60
    mm = minutes_from_9 % 60
    return f"{hh:02d}:{mm:02d}"

print("SOLUTION:")
print(f"Day: {days[day_val]}")
print(f"Start Time: {to_hhmm(start_val)}")
print(f"End Time: {to_hhmm(end_val)}")