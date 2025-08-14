participants = {
    'Daniel': [],
    'Kathleen': [(330, 390)],
    'Carolyn': [(180, 210), (240, 270)],
    'Roger': [],
    'Cheryl': [(0, 30), (60, 150), (210, 270), (300, 480)],
    'Virginia': [(30, 150), (180, 210), (240, 270), (330, 390), (420, 480)],
    'Angela': [(30, 60), (90, 150), (180, 210), (240, 270), (300, 450)]
}

def minutes_to_time(minutes):
    hours = 9 + (minutes // 60)
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

for start in range(0, 451):
    end = start + 30
    if start < 210:  # Roger's preference
        continue
    valid = True
    for busy_intervals in participants.values():
        for b_start, b_end in busy_intervals:
            if start < b_end and end > b_start:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"{start_time}:{end_time} Monday")
        break