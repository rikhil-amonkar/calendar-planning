def to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

participants = {
    'Patrick': [(810, 840), (870, 900)],
    'Shirley': [(540, 570), (660, 690), (720, 750), (870, 900), (960, 1020)],
    'Jeffrey': [(540, 570), (630, 660), (690, 720), (780, 810), (960, 1020)],
    'Gloria': [(690, 720), (900, 930)],
    'Nathan': [(540, 570), (630, 720), (840, 1020)],
    'Angela': [(540, 570), (600, 660), (750, 900), (930, 990)],
    'David': [(540, 570), (600, 630), (660, 840), (870, 990)]
}

for start in range(540, 991):  # 990 is the last possible start time (16:30)
    end = start + 30
    valid = True
    for busy_list in participants.values():
        for (bs, be) in busy_list:
            if not (end <= bs or start >= be):  # Check for overlap
                valid = False
                break
        if not valid:
            break
    if valid:
        start_time = to_time(start)
        end_time = to_time(end)
        print(f"{start_time}:{end_time} Monday")
        break