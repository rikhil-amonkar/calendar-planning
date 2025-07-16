def min_to_time_str(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Define available intervals (in minutes from 9:00, [start, end))
evelyn_available = [(0, 240)]  # 9:00 to 13:00 (exclusive)
randy_available = [(90, 120), (390, 420)]  # 10:30-11:00 and 15:30-16:00

duration = 30  # Meeting duration in minutes

found = False
slot_start = None
for r_int in randy_available:
    for e_int in evelyn_available:
        start_overlap = max(r_int[0], e_int[0])
        end_overlap = min(r_int[1], e_int[1])
        if end_overlap - start_overlap >= duration:
            slot_start = start_overlap
            found = True
            break
    if found:
        break

if found:
    start_str = min_to_time_str(slot_start)
    end_str = min_to_time_str(slot_start + duration)
    time_output = start_str + ":" + end_str
    print("Monday")
    print(time_output)
else:
    print("No suitable time found.")