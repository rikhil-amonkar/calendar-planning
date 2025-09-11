def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_available_intervals(busy_intervals):
    work_start = 9 * 60
    work_end = 17 * 60
    sorted_busies = sorted(busy_intervals, key=lambda x: x[0])
    available = []
    prev_end = work_start
    for start, end in sorted_busies:
        if prev_end < start:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end <= work_end:
        available.append((prev_end, work_end))
    return available

# Define busy intervals for each participant
busy_cynthia = [
    (9*60 + 30, 10*60 + 30),  # 9:30-10:30
    (11*60 + 30, 12*60 + 0),  # 11:30-12:00
    (13*60 + 0, 13*60 + 30),  # 13:00-13:30
    (15*60 + 0, 16*60 + 0),   # 15:00-16:00
]

busy_lauren = [
    (9*60 + 0, 9*60 + 30),  # 9:00-9:30
    (10*60 + 30, 11*60 + 0),  # 10:30-11:00
    (11*60 + 30, 12*60 + 0),  # 11:30-12:00
    (13*60 + 0, 13*60 + 30),  # 13:00-13:30
    (14*60 + 0, 14*60 + 30),  # 14:00-14:30
    (15*60 + 0, 15*60 + 30),  # 15:00-15:30
    (16*60 + 0, 17*60 + 0),   # 16:00-17:00
]

busy_robert = [
    (10*60 + 30, 11*60 + 0),  # 10:30-11:00
    (11*60 + 30, 12*60 + 0),  # 11:30-12:00
    (12*60 + 30, 13*60 + 30),  # 12:30-13:30
    (14*60 + 0, 16*60 + 0),   # 14:00-16:00
]

busy_steven = []
busy_roy = []

# Generate available intervals for each participant
available_cynthia = get_available_intervals(busy_cynthia)
available_lauren = get_available_intervals(busy_lauren)
available_robert = get_available_intervals(busy_robert)
available_steven = get_available_intervals(busy_steven)
available_roy = get_available_intervals(busy_roy)

participants_available = [
    available_cynthia,
    available_lauren,
    available_robert,
    available_steven,
    available_roy
]

# Find the earliest 30-minute slot
work_start = 9 * 60
work_end = 17 * 60
duration = 30

for start in range(work_start, work_end - duration + 1):
    end = start + duration
    all_available = True
    for available in participants_available:
        found = False
        for a_start, a_end in available:
            if a_start <= start and end <= a_end:
                found = True
                break
        if not found:
            all_available = False
            break
    if all_available:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"{start_time}:{end_time} Monday")
        break