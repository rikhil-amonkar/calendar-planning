# Meeting parameters
DURATION = 30  # minutes (0.5 hours)
WORK_START = 9 * 60
WORK_END = 17 * 60
DAY = "Monday"

# Busy intervals for each participant as (start_min, end_min) in minutes since 00:00
def minutes(h, m):
    return h * 60 + m

patrick_busy = [
    (minutes(9, 0),  minutes(9, 30)),
    (minutes(10, 0), minutes(10, 30)),
    (minutes(13, 30), minutes(14, 0)),
    (minutes(16, 0), minutes(16, 30)),
]

kayla_busy = [
    (minutes(12, 30), minutes(13, 30)),
    (minutes(15, 0), minutes(15, 30)),
    (minutes(16, 0), minutes(16, 30)),
]

carl_busy = [
    (minutes(10, 30), minutes(11, 0)),
    (minutes(12, 0),  minutes(12, 30)),
    (minutes(13, 0),  minutes(13, 30)),
    (minutes(14, 30), minutes(17, 0)),
]

christian_busy = [
    (minutes(9, 0),  minutes(12, 30)),
    (minutes(13, 0), minutes(14, 0)),
    (minutes(14, 30), minutes(17, 0)),
]

participants_busy = [patrick_busy, kayla_busy, carl_busy, christian_busy]

def overlaps(s, e, busy_list):
    # overlap if not (meeting ends before busy starts or starts after busy ends)
    for b_start, b_end in busy_list:
        if not (e <= b_start or s >= b_end):
            return True
    return False

def fmt(mm):
    hh = mm // 60
    mi = mm % 60
    return f"{hh:02d}:{mi:02d}"

# Search in 30-minute increments for the earliest feasible slot
found = None
for start in range(WORK_START, WORK_END - DURATION + 1, 30):
    end = start + DURATION
    feasible = True
    for busy in participants_busy:
        if overlaps(start, end, busy):
            feasible = False
            break
    if feasible:
        found = (start, end)
        break

if found:
    s, e = found
    # Ensure exact duration of 0.5 hours
    assert e - s == DURATION, "Duration mismatch"
    plan = {'day': DAY, 'time_range': f"{{{fmt(s)}:{fmt(e)}}}"}
    print(plan)
else:
    print("No feasible time found.")