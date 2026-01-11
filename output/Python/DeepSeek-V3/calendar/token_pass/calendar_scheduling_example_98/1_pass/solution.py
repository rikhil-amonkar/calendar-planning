def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Work hours
work_start = time_to_min("9:00")
work_end = time_to_min("17:00")

# Busy intervals in minutes from midnight? No, from 0=9:00.
# But easier to do absolute minutes from 0:00.
def t_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Busy times (absolute minutes from midnight)
busy = {
    "Juan": [(t_min("9:00"), t_min("10:30")), (t_min("15:30"), t_min("16:00"))],
    "Marilyn": [(t_min("11:00"), t_min("11:30")), (t_min("12:30"), t_min("13:00"))],
    "Ronald": [(t_min("9:00"), t_min("10:30")), (t_min("12:00"), t_min("12:30")),
               (t_min("13:00"), t_min("13:30")), (t_min("14:00"), t_min("16:30"))]
}

# Juan cannot meet after 16:00 means meeting end <= t_min("16:00")
meeting_duration = 30

# Search from 9:00 to 16:30 (since 30 min meeting)
for start_min in range(t_min("9:00"), t_min("16:30") + 1):
    end_min = start_min + meeting_duration
    if end_min > t_min("17:00"):
        continue
    # Juan's constraint: end <= 16:00
    if end_min > t_min("16:00"):
        continue
    
    ok = True
    for person, intervals in busy.items():
        for s, e in intervals:
            if not (end_min <= s or start_min >= e):
                ok = False
                break
        if not ok:
            break
    if ok:
        print(f"Monday {min_to_time(start_min)}:{min_to_time(end_min)}")
        break