def time_to_minutes(t_str):
    # Convert HH:MM string to minutes from midnight
    h, m = map(int, t_str.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes from midnight to HH:MM string
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    # busy_intervals: list of tuples (start, end) in minutes
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for b_start, b_end in busy_intervals:
        if b_start > current:
            free_intervals.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(list1, list2):
    # Compute intersection of two lists of intervals.
    result = []
    i, j = 0, 0
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        inter_start = max(start1, start2)
        inter_end = min(end1, end2)
        if inter_start < inter_end:
            result.append((inter_start, inter_end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Define work hours in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Busy schedules for each participant (in minutes)
# Nicole's busy intervals by day
busy_nicole = {
    "Monday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
               (time_to_minutes("13:00"), time_to_minutes("13:30")),
               (time_to_minutes("14:30"), time_to_minutes("15:30"))],
    "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                (time_to_minutes("11:30"), time_to_minutes("13:30")),
                (time_to_minutes("14:30"), time_to_minutes("15:30"))],
    "Wednesday": [(time_to_minutes("10:00"), time_to_minutes("11:00")),
                  (time_to_minutes("12:30"), time_to_minutes("15:00")),
                  (time_to_minutes("16:00"), time_to_minutes("17:00"))]
}

# Ruth's busy intervals by day
busy_ruth = {
    "Monday": [(time_to_minutes("09:00"), time_to_minutes("17:00"))],
    "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("17:00"))],
    "Wednesday": [(time_to_minutes("09:00"), time_to_minutes("10:30")),
                  (time_to_minutes("11:00"), time_to_minutes("11:30")),
                  (time_to_minutes("12:00"), time_to_minutes("12:30")),
                  (time_to_minutes("13:30"), time_to_minutes("15:30")),
                  (time_to_minutes("16:00"), time_to_minutes("16:30"))]
}

# Additional constraint:
# Ruth does not want to meet on Wednesday after 13:30, so restrict any meeting on Wednesday to end by 13:30.
# We can enforce this by adding a "busy" block from 13:30 to work_end for Ruth on Wednesday.
additional_ruth = {
    "Wednesday": [(time_to_minutes("13:30"), work_end)]
}

# Merge Ruth's busy intervals with additional constraint on Wednesday
for day in additional_ruth:
    busy_ruth[day].extend(additional_ruth[day])
    busy_ruth[day] = sorted(busy_ruth[day], key=lambda x: x[0])

# Days to consider
days = ["Monday", "Tuesday", "Wednesday"]

scheduled_day = None
scheduled_start = None
scheduled_end = None

for day in days:
    # Get free intervals for each participant for the day.
    free_nicole = get_free_intervals(work_start, work_end, busy_nicole.get(day, []))
    free_ruth = get_free_intervals(work_start, work_end, busy_ruth.get(day, []))
    # Get common free intervals
    common_free = intersect_intervals(free_nicole, free_ruth)
    # Check if any common interval can accommodate the meeting_duration.
    for interval in common_free:
        start, end = interval
        if end - start >= meeting_duration:
            scheduled_day = day
            scheduled_start = start
            scheduled_end = start + meeting_duration
            break
    if scheduled_day:
        break

if scheduled_day:
    meeting_time = f"{minutes_to_time(scheduled_start)}:{minutes_to_time(scheduled_end)}"
    print(f"{scheduled_day} {meeting_time}")
else:
    print("No suitable meeting time found.")