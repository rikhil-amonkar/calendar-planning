participants = {
    'Christine': [(570, 630), (720, 750), (780, 810), (870, 900), (960, 990)],
    'Bobby': [(720, 750), (870, 900)],
    'Elizabeth': [(540, 570), (690, 780), (810, 840), (900, 930), (960, 1020)],
    'Tyler': [(540, 660), (720, 750), (780, 810), (930, 960), (990, 1020)],
    'Edward': [(540, 570), (600, 660), (690, 840), (870, 930), (960, 1020)],
    'Janice': []
}


def compute_free_intervals(busy_intervals):
    start_work = 540
    end_work = 1020
    busy_intervals.sort()
    free_intervals = []
    prev_end = start_work
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_work:
        free_intervals.append((prev_end, end_work))
    return free_intervals


# Compute free intervals for each participant
free_intervals = {}
for name, busy in participants.items():
    free_intervals[name] = compute_free_intervals(busy)

# Now find the earliest valid time
start_work = 540
end_work = 1020
meeting_duration = 30


def to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"


for candidate_start in range(start_work, end_work - meeting_duration + 1):
    candidate_end = candidate_start + meeting_duration
    valid = True
    for name in participants:
        found = False
        for (s, e) in free_intervals[name]:
            if s <= candidate_start and candidate_end <= e:
                found = True
                break
        if not found:
            valid = False
            break
    if valid:
        start_time = to_time(candidate_start)
        end_time = to_time(candidate_end)
        day = "Monday"
        print(f"{{{start_time}:{end_time}}} {day}")
        break
