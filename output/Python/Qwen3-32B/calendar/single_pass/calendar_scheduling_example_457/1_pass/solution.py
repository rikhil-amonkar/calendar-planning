participants_busy = {
    'Andrea': [(570, 630), (810, 870)],
    'Ruth': [(750, 780), (900, 930)],
    'Steven': [(600, 630), (660, 690), (720, 750), (810, 840), (900, 960)],
    'Grace': [],
    'Kyle': [(540, 570), (630, 720), (750, 780), (810, 900), (930, 960), (990, 1020)],
    'Elijah': [(540, 660), (690, 780), (810, 840), (930, 960), (990, 1020)],
    'Lori': [(540, 570), (600, 690), (720, 810), (840, 960), (990, 1020)]
}

for t in range(540, 1020, 30):
    candidate_end = t + 30
    valid = True
    for busy_intervals in participants_busy.values():
        for start, end in busy_intervals:
            if t < end and candidate_end > start:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_h = t // 60
        start_m = t % 60
        end_h = candidate_end // 60
        end_m = candidate_end % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_time = f"{end_h:02d}:{end_m:02d}"
        print(f"{start_time}:{end_time} Monday")
        break