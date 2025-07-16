def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    total_minutes = hour * 60 + minute
    base = 9 * 60  # 9:00 in minutes from midnight
    return total_minutes - base

participants_busy = {
    'Megan': ["9:00 to 9:30", "10:00 to 11:00", "12:00 to 12:30"],
    'Christine': ["9:00 to 9:30", "11:30 to 12:00", "13:00 to 14:00", "15:30 to 16:30"],
    'Gabriel': [],
    'Sara': ["11:30 to 12:00", "14:30 to 15:00"],
    'Bruce': ["9:30 to 10:00", "10:30 to 12:00", "12:30 to 14:00", "14:30 to 15:00", "15:30 to 16:30"],
    'Kathryn': ["10:00 to 15:30", "16:00 to 16:30"],
    'Billy': ["9:00 to 9:30", "11:00 to 11:30", "12:00 to 14:00", "14:30 to 15:30"]
}

busy_intervals = []

for person, intervals in participants_busy.items():
    for interval in intervals:
        parts = interval.split(' to ')
        start_str = parts[0].strip()
        end_str = parts[1].strip()
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        busy_intervals.append((start_min, end_min))

busy_intervals.sort(key=lambda x: x[0])

merged = []
if busy_intervals:
    merged = [busy_intervals[0]]
    for i in range(1, len(busy_intervals)):
        current_start, current_end = busy_intervals[i]
        last_start, last_end = merged[-1]
        if current_start <= last_end:
            merged[-1] = (last_start, max(last_end, current_end))
        else:
            merged.append((current_start, current_end))

free_intervals = []
current_start = 0
for start, end in merged:
    if current_start < start:
        free_intervals.append((current_start, start))
    current_start = end
if current_start < 480:
    free_intervals.append((current_start, 480))

meeting_slot = None
for start, end in free_intervals:
    if end - start >= 30:
        meeting_slot = (start, start + 30)
        break

if meeting_slot:
    s = meeting_slot[0]
    meeting_start_abs = 9 * 60 + s
    start_hour = meeting_start_abs // 60
    start_minute = meeting_start_abs % 60
    meeting_end_abs = meeting_start_abs + 30
    end_hour = meeting_end_abs // 60
    end_minute = meeting_end_abs % 60
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print("Monday")
    print(time_str)
else:
    print("No suitable meeting time found.")