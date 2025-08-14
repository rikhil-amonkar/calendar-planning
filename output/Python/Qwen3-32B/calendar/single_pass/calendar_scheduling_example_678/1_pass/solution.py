# Helper functions
def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_times(busy_times, work_start=9*60, work_end=17*60):
    busy_times_sorted = sorted(busy_times, key=lambda x: x[0])
    free_times = []
    prev_end = work_start
    for start, end in busy_times_sorted:
        if start > prev_end:
            free_times.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_times.append((prev_end, work_end))
    return free_times

def adjust_for_russell_tue(free_times):
    adjusted = []
    for start, end in free_times:
        new_start = max(start, 13*60 + 30)  # 13:30 is 810 minutes
        if new_start < end:
            adjusted.append((new_start, end))
    return adjusted

def find_overlap(r_free, a_free):
    for r_start, r_end in r_free:
        for a_start, a_end in a_free:
            overlap_start = max(r_start, a_start)
            overlap_end = min(r_end, a_end)
            if overlap_start < overlap_end:
                if overlap_end - overlap_start >= 60:
                    return (overlap_start, overlap_start + 60)
    return None

# Define busy times for each participant on each day
russell_mon_busy = [(10*60 + 30, 11*60 + 0)]  # 10:30-11:00
russell_tue_busy = [(13*60 + 0, 13*60 + 30)]  # 13:00-13:30

alexander_mon_busy = [
    (9*60 + 0, 11*60 + 30),  # 9:00-11:30
    (12*60 + 0, 14*60 + 30),  # 12:00-14:30
    (15*60 + 0, 17*60 + 0)   # 15:00-17:00
]
alexander_tue_busy = [
    (9*60 + 0, 10*60 + 0),   # 9:00-10:00
    (13*60 + 0, 14*60 + 0),  # 13:00-14:00
    (15*60 + 0, 15*60 + 30), # 15:00-15:30
    (16*60 + 0, 16*60 + 30)  # 16:00-16:30
]

# Process Monday
russell_mon_free = get_free_times(russell_mon_busy)
alexander_mon_free = get_free_times(alexander_mon_busy)
mon_overlap = find_overlap(russell_mon_free, alexander_mon_free)

# Process Tuesday
russell_tue_free = get_free_times(russell_tue_busy)
russell_tue_free = adjust_for_russell_tue(russell_tue_free)
alexander_tue_free = get_free_times(alexander_tue_busy)
tue_overlap = find_overlap(russell_tue_free, alexander_tue_free)

# Determine the result
result = None
day = None
if mon_overlap:
    result = mon_overlap
    day = "Monday"
elif tue_overlap:
    result = tue_overlap
    day = "Tuesday"

# Output the result
if result:
    start_time = minutes_to_time_str(result[0])
    end_time = minutes_to_time_str(result[1])
    print(f"{start_time}:{end_time} {day}")