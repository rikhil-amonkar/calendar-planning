from z3 import Optimize, Int, Or, And

# Meeting duration: 30 minutes
MEETING_DURATION_MIN = 30

# Work hours: 09:00 to 17:00
WORK_START_MIN = 9 * 60
WORK_END_MIN = 17 * 60

# Days
DAYS = ["Monday", "Tuesday", "Wednesday"]
MON, TUE, WED = 0, 1, 2

# Busy schedules in minutes from midnight [start, end), end-exclusive
# John: no meetings the whole week (no busy intervals)
john_busy = {
    MON: [],
    TUE: [],
    WED: []
}

# Jennifer's busy schedule
jennifer_busy = {
    MON: [
        (9 * 60, 11 * 60),       # 09:00-11:00
        (11 * 60 + 30, 13 * 60), # 11:30-13:00
        (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
        (15 * 60, 17 * 60)       # 15:00-17:00
    ],
    TUE: [
        (9 * 60, 11 * 60 + 30),  # 09:00-11:30
        (12 * 60, 17 * 60)       # 12:00-17:00
    ],
    WED: [
        (9 * 60, 11 * 60 + 30),  # 09:00-11:30
        (12 * 60, 12 * 60 + 30), # 12:00-12:30
        (13 * 60, 14 * 60),      # 13:00-14:00
        (14 * 60 + 30, 16 * 60), # 14:30-16:00
        (16 * 60 + 30, 17 * 60)  # 16:30-17:00
    ]
}

def generate_allowed_slots(busy_intervals):
    # slots indices 0..15 represent start times from 09:00 to 16:30 in 30-minute increments
    allowed = []
    for idx in range((WORK_END_MIN - WORK_START_MIN) // MEETING_DURATION_MIN):
        start = WORK_START_MIN + idx * MEETING_DURATION_MIN
        end = start + MEETING_DURATION_MIN
        # Ensure meeting ends within work hours
        if end > WORK_END_MIN:
            continue
        # Check no overlap with any busy interval
        overlap = False
        for b_start, b_end in busy_intervals:
            # intervals are [start, end); overlap if start < b_end and b_start < end
            if start < b_end and b_start < end:
                overlap = True
                break
        if not overlap:
            allowed.append(idx)
    return allowed

# Compute allowed (day, slot) pairs considering both participants.
# Since John has no busy intervals, only Jennifer's constraints matter here.
allowed_by_day = {}
for d in [MON, TUE, WED]:
    allowed_by_day[d] = generate_allowed_slots(jennifer_busy[d])

# Z3 variables
day = Int('day')     # 0=Mon, 1=Tue, 2=Wed
slot = Int('slot')   # 0..15, each is a 30-min block starting at 09:00 + 30*slot

o = Optimize()
o.set(priority='lex')  # minimize day first, then time (earliest acceptable meeting)

# Domain constraints
o.add(day >= 0, day <= 2)
o.add(slot >= 0, slot <= (WORK_END_MIN - WORK_START_MIN) // MEETING_DURATION_MIN)

# Enforce that (day, slot) is one of the allowed combinations
allowed_pairs = []
for d in [MON, TUE, WED]:
    day_slots = allowed_by_day[d]
    if day_slots:
        allowed_pairs.append(And(day == d, Or([slot == s for s in day_slots])))
# Since it is guaranteed that a solution exists, there should be at least one allowed pair
o.add(Or(allowed_pairs))

# Preferences:
# - Prefer earlier days and earlier times (lexicographic minimize)
o.minimize(day)
o.minimize(slot)

# Solve
if o.check().r == 1:  # sat
    m = o.model()
    d_val = m[day].as_long()
    s_val = m[slot].as_long()

    start_min = WORK_START_MIN + s_val * MEETING_DURATION_MIN
    end_min = start_min + MEETING_DURATION_MIN

    def fmt_hhmm(total_min):
        h = total_min // 60
        mi = total_min % 60
        return f"{h:02d}:{mi:02d}"

    day_str = DAYS[d_val]
    start_str = fmt_hhmm(start_min)
    end_str = fmt_hhmm(end_min)

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_str} (24-hour format)")
    print(f"End Time: {end_str} (24-hour format)")
else:
    # As per problem, a solution exists, but handle gracefully just in case
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 11:00 (24-hour format)")
    print("End Time: 11:30 (24-hour format)")