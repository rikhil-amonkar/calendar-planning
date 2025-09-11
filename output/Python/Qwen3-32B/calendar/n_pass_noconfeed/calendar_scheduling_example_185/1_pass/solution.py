def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

busy_kimberly = [(600, 630), (660, 720), (960, 990)]
busy_megan = []
busy_marie = [(600, 660), (690, 900), (960, 990)]
busy_diana = [(570, 600), (630, 870), (930, 1020)]

def is_free(start, busy_intervals):
    end = start + 30
    for b_start, b_end in busy_intervals:
        if start < b_end and b_start < end:
            return False
    return True

for start_time_min in range(600, 991):  # 990 is inclusive
    if (is_free(start_time_min, busy_kimberly) and
        is_free(start_time_min, busy_megan) and
        is_free(start_time_min, busy_marie) and
        is_free(start_time_min, busy_diana)):
        start_str = to_time_str(start_time_min)
        end_str = to_time_str(start_time_min + 30)
        print(f"{start_str}:{end_str} Monday")
        break