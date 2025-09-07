from z3 import *

# Days: 0=Monday, 1=Tuesday, 2=Wednesday
day_names = ["Monday", "Tuesday", "Wednesday"]

# Time slots: 30-minute slots from 09:00 to 16:30 inclusive (start times)
# slot s corresponds to time 09:00 + 30*s
SLOTS_PER_DAY = 16  # 09:00..16:30 start times

# Busy slots per participant per day
# (computed as the set of 30-min start slots that overlap their meetings)
busy = {
    "Arthur": {
        0: [4, 9, 12],              # Mon: 11:00, 13:30, 15:00
        1: [8, 14],                 # Tue: 13:00, 16:00
        2: [2, 4, 6, 10, 14],       # Wed: 10:00, 11:00, 12:00, 14:00, 16:00
    },
    "Michael": {
        0: list(range(0, 6)) + [7, 10] + list(range(12, 16)),  # Mon: 09:00-12:00, 12:30, 14:00, 15:00-17:00
        1: list(range(1, 6)) + list(range(6, 9)) + list(range(10, 13)),  # Tue: 09:30-11:30, 12:00-13:30, 14:00-15:30
        2: list(range(2, 7)) + [8],   # Wed: 10:00-12:30, 13:00
    }
}

# Z3 variables
d = Int('day')     # 0..2
s = Int('slot')    # 0..15 (start slot within the workday)

opt = Optimize()

# Domain constraints
opt.add(d >= 0, d <= 2)
opt.add(s >= 0, s < SLOTS_PER_DAY)

# Work hours are already captured by limiting slots to 0..15 (09:00..16:30 start).
# Arthur cannot meet on Tuesday
opt.add(d != 1)

# No overlap with busy times for each participant on the chosen day
for person in busy:
    for day_idx in range(3):
        blocked = busy[person][day_idx]
        # If this day is selected, the start slot must not be any blocked slot
        if blocked:
            opt.add(Implies(d == day_idx, And([s != b for b in blocked])))
        else:
            opt.add(Implies(d == day_idx, True))

# Preference: earliest availability (minimize day, then slot)
opt.minimize(d)
opt.minimize(s)

if opt.check() != sat:
    print("No solution found")
else:
    model = opt.model()
    day_val = model[d].as_long()
    slot_val = model[s].as_long()

    # Convert slot to HH:MM
    start_minutes = 9 * 60 + 30 * slot_val
    end_minutes = start_minutes + 30

    def fmt(m):
        h = m // 60
        mi = m % 60
        return f"{h:02d}:{mi:02d}"

    start_str = fmt(start_minutes)
    end_str = fmt(end_minutes)
    day_str = day_names[day_val]

    # Output includes both day and time range in {HH:MM:HH:MM}
    print(f"{day_str} {{{start_str}:{end_str}}}")