def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

busy_schedules = {
    'Jose': [(660, 690), (750, 780)],
    'Keith': [(840, 870), (900, 930)],
    'Logan': [(540, 600), (720, 750), (900, 930)],
    'Megan': [(540, 630), (660, 720), (780, 810), (870, 990)],
    'Gary': [(540, 570), (600, 630), (690, 780), (810, 840), (870, 990)],
    'Bobby': [(660, 690), (720, 750), (780, 960)]
}

for start in range(540, 901):
    end = start + 30
    conflict = False
    for person in busy_schedules:
        for (bs, be) in busy_schedules[person]:
            if not (end <= bs or start >= be):
                conflict = True
                break
        if conflict:
            break
    if not conflict:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        day = "Monday"
        print(f"{start_time}:{end_time} {day}")
        break