def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define busy times for Nicole and Daniel
nicole_busy = {
    'Monday': [],
    'Tuesday': [(16*60, 16*60 + 30)],
    'Wednesday': [(15*60, 15*60 + 30)],
    'Thursday': [],
    'Friday': [(12*60, 12*60 + 30), (15*60 + 30, 16*60)]
}

daniel_busy = {
    'Monday': [
        (9*60, 12*60 + 30),  # 9:00-12:30
        (13*60, 13*60 + 30), # 13:00-13:30
        (14*60, 16*60 + 30)  # 14:00-16:30
    ],
    'Tuesday': [
        (9*60, 10*60 + 30),   # 9:00-10:30
        (11*60 + 30, 12*60 + 30), # 11:30-12:30
        (13*60, 13*60 + 30), # 13:00-13:30
        (15*60, 16*60),      # 15:00-16:00
        (16*60 + 30, 17*60)  # 16:30-17:00
    ],
    'Wednesday': [
        (9*60, 10*60),        # 9:00-10:00
        (11*60, 12*60 + 30),  # 11:00-12:30
        (13*60, 13*60 + 30),  # 13:00-13:30
        (14*60, 14*60 + 30),  # 14:00-14:30
        (16*60 + 30, 17*60)   # 16:30-17:00
    ],
    'Thursday': [
        (11*60, 12*60),       # 11:00-12:00
        (13*60, 14*60),       # 13:00-14:00
        (15*60, 15*60 + 30)   # 15:00-15:30
    ],
    'Friday': [
        (10*60, 11*60),       # 10:00-11:00
        (11*60 + 30, 12*60),  # 11:30-12:00
        (12*60 + 30, 14*60 + 30), # 12:30-14:30
        (15*60, 15*60 + 30),  # 15:00-15:30
        (16*60, 16*60 + 30)   # 16:00-16:30
    ]
}

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
start_work = 9 * 60
end_work = 17 * 60

candidates = []

for day in days:
    combined = nicole_busy[day] + daniel_busy[day]
    sorted_buses = sorted(combined, key=lambda x: x[0])
    free_intervals = []
    prev_end = start_work
    for bus in sorted_buses:
        bus_start, bus_end = bus
        if prev_end < bus_start:
            free_intervals.append((prev_end, bus_start))
        prev_end = max(prev_end, bus_end)
    if prev_end < end_work:
        free_intervals.append((prev_end, end_work))
    for (s, e) in free_intervals:
        if e - s >= 60:
            candidates.append((s, s + 60, day))

# Find the earliest candidate
earliest = min(candidates, key=lambda x: x[0])

start_minutes, end_minutes, day = earliest

start_time = to_time(start_minutes)
end_time = to_time(end_minutes)

print(f"{start_time}:{end_time} {day}")