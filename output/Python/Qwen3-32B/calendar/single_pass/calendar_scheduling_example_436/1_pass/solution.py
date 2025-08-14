participants = {
    'Patrick': [(810, 840), (870, 900)],
    'Shirley': [(540, 570), (660, 690), (720, 750), (870, 900), (960, 1020)],
    'Jeffrey': [(540, 570), (630, 660), (690, 720), (780, 810), (960, 1020)],
    'Gloria': [(690, 720), (900, 930)],
    'Nathan': [(540, 570), (630, 720), (840, 1020)],
    'Angela': [(540, 570), (600, 660), (750, 900), (930, 990)],
    'David': [(540, 570), (600, 630), (660, 840), (870, 990)]
}

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

for start in range(540, 991):  # 990 is 16:30, 990+1=991 to include 990
    valid = True
    for busy_intervals in participants.values():
        for b_start, b_end in busy_intervals:
            # Check if [start, start+30) overlaps with [b_start, b_end)
            if start < b_end and start + 30 > b_start:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(start + 30)
        print(f"{start_time}:{end_time} Monday")
        break