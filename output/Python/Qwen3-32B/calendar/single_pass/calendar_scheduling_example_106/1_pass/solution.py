def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

olivia_busy = [(750, 810), (870, 900), (990, 1020)]
anna_busy = []
virginia_busy = [(540, 600), (690, 960), (990, 1020)]
paul_busy = [(540, 570), (660, 690), (780, 840), (870, 960), (990, 1020)]

for start in range(540, 960 + 1):
    meeting_end = start + 60
    valid = True
    for person_busy in [olivia_busy, anna_busy, virginia_busy, paul_busy]:
        for b_start, b_end in person_busy:
            if not (meeting_end <= b_start or b_end <= start):
                valid = False
                break
        if not valid:
            break
    if valid:
        start_str = time_to_str(start)
        end_str = time_to_str(meeting_end)
        print(f"{start_str}:{end_str} Monday")
        break