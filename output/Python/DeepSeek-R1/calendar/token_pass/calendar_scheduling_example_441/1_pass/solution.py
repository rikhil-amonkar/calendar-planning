def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 30

busy_intervals = []

joan_schedule = ["11:30 to 12:00", "14:30 to 15:00"]
megan_schedule = ["9:00 to 10:00", "14:00 to 14:30", "16:00 to 16:30"]
austin_schedule = []
betty_schedule = ["9:30 to 10:00", "11:30 to 12:00", "13:30 to 14:00", "16:00 to 16:30"]
judith_schedule = ["9:00 to 11:00", "12:00 to 13:00", "14:00 to 15:00"]
terry_schedule = ["9:30 to 10:00", "11:30 to 12:30", "13:00 to 14:00", "15:00 to 15:30", "16:00 to 17:00"]
kathryn_schedule = ["9:30 to 10:00", "10:30 to 11:00", "11:30 to 13:00", "14:00 to 16:00", "16:30 to 17:00"]

schedules = [joan_schedule, megan_schedule, austin_schedule, betty_schedule, judith_schedule, terry_schedule, kathryn_schedule]

for schedule in schedules:
    for interval in schedule:
        start_str, end_str = interval.split(" to ")
        start_minutes = time_to_minutes(start_str)
        end_minutes = time_to_minutes(end_str)
        busy_intervals.append((start_minutes, end_minutes))

busy_intervals.sort(key=lambda x: x[0])

merged = []
for start, end in busy_intervals:
    if not merged:
        merged.append([start, end])
    else:
        last_end = merged[-1][1]
        if start <= last_end:
            merged[-1][1] = max(last_end, end)
        else:
            merged.append([start, end])

free_slots = []
current = work_start
for start, end in merged:
    if current < start:
        free_slots.append((current, start))
    current = max(current, end)
if current < work_end:
    free_slots.append((current, work_end))

for start, end in free_slots:
    if end - start >= duration:
        meeting_start = start
        meeting_end = meeting_start + duration
        break

start_time_str = minutes_to_time(meeting_start)
end_time_str = minutes_to_time(meeting_end)

print(f"Monday {start_time_str}:{end_time_str}")