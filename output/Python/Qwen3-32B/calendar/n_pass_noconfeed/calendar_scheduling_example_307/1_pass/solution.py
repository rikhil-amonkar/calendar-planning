participants = {
    'ronald': [],
    'stephen': [(600, 630), (720, 750)],
    'brittany': [(660, 690), (810, 840), (930, 960), (990, 1020)],
    'dorothy': [(540, 570), (600, 630), (660, 750), (780, 900), (930, 1020)],
    'rebecca': [(570, 630), (660, 690), (720, 750), (780, 1020)],
    'jordan': [(540, 570), (600, 660), (690, 720), (780, 900), (930, 990)]
}

work_start = 540  # 9:00 AM in minutes
work_end = 1020   # 5:00 PM in minutes
meeting_duration = 30  # minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

found = False
for start in range(work_start, work_end - meeting_duration + 1):
    feasible = True
    for busy_times in participants.values():
        for (bs, be) in busy_times:
            if not (start + meeting_duration <= bs or start >= be):
                feasible = False
                break
        if not feasible:
            break
    if feasible:
        found = True
        break

if found:
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(start + meeting_duration)
    print(f"{start_time}:{end_time} Monday")