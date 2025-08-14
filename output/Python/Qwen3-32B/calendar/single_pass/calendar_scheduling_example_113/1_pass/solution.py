participants = {
    'Bradley': [(570, 600), (750, 780), (810, 840), (930, 960)],
    'Teresa': [(630, 660), (720, 750), (780, 810), (870, 900)],
    'Elizabeth': [(540, 570), (630, 690), (780, 810), (870, 900), (930, 1020)],
    'Christian': [(540, 570), (630, 1020)]
}

day = 'Monday'

for start in range(540, 991):  # 9:00 to 16:30 in minutes
    end = start + 30
    valid = True
    for busy_intervals in participants.values():
        for (bus_start, bus_end) in busy_intervals:
            if bus_end > start and bus_start < end:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_h = start // 60
        start_m = start % 60
        end_h = end // 60
        end_m = end % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_time = f"{end_h:02d}:{end_m:02d}"
        print(f"{{{start_time}:{end_time}}} {day}")
        break