def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_start = 9 * 60
work_end = 17 * 60
duration = 30

blocked = {
    'Joe': [(570, 600), (630, 660)],
    'Keith': [(690, 720), (900, 930)],
    'Patricia': [(540, 570), (780, 810)],
    'Nancy': [(540, 660), (690, 990)],
    'Pamela': [(540, 600), (630, 660), (690, 750), (780, 840), (870, 900), (930, 960), (990, 1020)]
}

for start_time in range(work_start, work_end - duration + 1):
    end_time = start_time + duration
    all_free = True
    for person_blocks in blocked.values():
        for b_start, b_end in person_blocks:
            if not (end_time <= b_start or start_time >= b_end):
                all_free = False
                break
        if not all_free:
            break
    if all_free:
        start_str = time_to_str(start_time)
        end_str = time_to_str(end_time)
        print(f"{start_str}:{end_str} Monday")
        break