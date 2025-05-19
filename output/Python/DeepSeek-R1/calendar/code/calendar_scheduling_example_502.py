def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02}:{mins:02}"

def get_busy_intervals(schedule):
    intervals = []
    for entry in schedule:
        start, end = entry.split(' to ')
        intervals.append((parse_time(start), parse_time(end)))
    intervals.sort()
    merged = []
    for start, end in intervals:
        if merged and merged[-1][1] >= start:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    return merged

def find_free_slots(busy, work_start, work_end):
    free = []
    prev_end = work_start
    for start, end in busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def find_meeting_time(jack_busy, charlotte_busy, duration, work_hours, max_start_time=None):
    work_start = parse_time(work_hours[0])
    work_end = parse_time(work_hours[1])
    
    jack_free = find_free_slots(get_busy_intervals(jack_busy), work_start, work_end)
    charlotte_free = find_free_slots(get_busy_intervals(charlotte_busy), work_start, work_end)
    
    common_slots = []
    i = j = 0
    while i < len(jack_free) and j < len(charlotte_free):
        j_start, j_end = jack_free[i]
        c_start, c_end = charlotte_free[j]
        
        start = max(j_start, c_start)
        end = min(j_end, c_end)
        if start < end:
            if max_start_time is None or start <= parse_time(max_start_time):
                common_slots.append((start, end))
            if j_end < c_end:
                i += 1
            else:
                j += 1
        else:
            if j_end <= c_start:
                i += 1
            else:
                j += 1
                
    for start, end in common_slots:
        if end - start >= duration:
            return (start, start + duration)
    return None

jack_schedule = [
    "9:30 to 10:30",
    "11:00 to 11:30",
    "12:30 to 13:00",
    "14:00 to 14:30",
    "16:00 to 16:30"
]

charlotte_schedule = [
    "9:30 to 10:00",
    "10:30 to 12:00",
    "12:30 to 13:30",
    "14:00 to 16:00"
]

meeting_duration = 30  # minutes
work_hours = ("9:00", "17:00")
max_start_time = "12:30"  # Jack's preference

slot = find_meeting_time(jack_schedule, charlotte_schedule, meeting_duration, work_hours, max_start_time)

if slot:
    start, end = slot
    print(f"{format_time(start)}:{format_time(end)}")
    print("Monday")
else:
    print("No suitable time found")