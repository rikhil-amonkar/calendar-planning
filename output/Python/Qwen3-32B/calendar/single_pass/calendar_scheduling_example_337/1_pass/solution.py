def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

participants = {
    'John': [(690, 720), (840, 870)],
    'Megan': [(720, 750), (840, 900), (930, 960)],
    'Brandon': [],
    'Kimberly': [(540, 570), (600, 630), (660, 870), (900, 960), (990, 1020)],
    'Sean': [(600, 660), (690, 840), (900, 930)],
    'Lori': [(540, 570), (630, 720), (780, 870), (960, 990)]
}

for start in range(540, 991):  # 9:00 to 16:30 in minutes
    end = start + 30
    all_free = True
    for busy_list in participants.values():
        for (s, e) in busy_list:
            if not (end <= s or start >= e):
                all_free = False
                break
        if not all_free:
            break
    if all_free:
        start_time = time_to_str(start)
        end_time = time_to_str(end)
        day = "Monday"
        print(f"{start_time}:{end_time} {day}")
        break