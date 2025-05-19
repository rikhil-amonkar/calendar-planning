def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

christine_blocked = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

helen_blocked = [
    (time_to_minutes("09:30"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]
helen_no_meet_after = time_to_minutes("15:00")

def get_available_slots(blocked, work_start, work_end, additional_constraint_end=None):
    blocked = sorted(blocked, key=lambda x: x[0])
    available = []
    current_start = work_start

    for start, end in blocked:
        if start > current_start:
            available.append((current_start, start))
        current_start = max(current_start, end)
    
    if current_start < work_end:
        available.append((current_start, work_end))
    
    if additional_constraint_end is not None:
        filtered = []
        for start, end in available:
            if end <= additional_constraint_end:
                filtered.append((start, end))
            elif start < additional_constraint_end:
                filtered.append((start, additional_constraint_end))
        available = filtered
    
    return available

christine_available = get_available_slots(christine_blocked, work_start, work_end)
christine_available = [(s, e) for s, e in christine_available if e > s]

helen_available = get_available_slots(helen_blocked, work_start, work_end, helen_no_meet_after)
helen_available = [(s, e) for s, e in helen_available if e > s]

def find_overlap(c_avail, h_avail, duration):
    for c_start, c_end in c_avail:
        for h_start, h_end in h_avail:
            start = max(c_start, h_start)
            end = min(c_end, h_end)
            if end - start >= duration:
                return (start, start + duration)
    return None

meeting_time = find_overlap(christine_available, helen_available, meeting_duration)

start_time = minutes_to_time(meeting_time[0])
end_time = minutes_to_time(meeting_time[1])

print(f"Monday {start_time}:{end_time}")