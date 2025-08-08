def time_to_minutes(timestr):
    hours, minutes = map(int, timestr.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Ensure busy intervals are sorted
    busy_intervals.sort(key=lambda x: x[0])
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(ints1, ints2):
    result = []
    i, j = 0, 0
    while i < len(ints1) and j < len(ints2):
        # find overlap between ints1[i] and ints2[j]
        start = max(ints1[i][0], ints2[j][0])
        end = min(ints1[i][1], ints2[j][1])
        if start < end:
            result.append((start, end))
        if ints1[i][1] < ints2[j][1]:
            i += 1
        else:
            j += 1
    return result

def main():
    # Define the working day: Monday 09:00 to 17:00 in minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    day = "Monday"
    meeting_duration = 30  # duration in minutes

    # Define each participant's busy intervals (in HH:MM format)
    schedules = {
        "Walter": [],  # No meetings
        "Cynthia": [("09:00", "09:30"), ("10:00", "10:30"), ("13:30", "14:30"), ("15:00", "16:00")],
        "Ann": [("10:00", "11:00"), ("13:00", "13:30"), ("14:00", "15:00"), ("16:00", "16:30")],
        "Catherine": [("09:00", "11:30"), ("12:30", "13:30"), ("14:30", "17:00")],
        "Kyle": [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:30"), ("15:00", "16:00")]
    }

    # Convert busy intervals to minutes and compute free intervals for each participant
    free_times = {}
    for person, intervals in schedules.items():
        busy_minutes = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]
        free_times[person] = get_free_intervals(busy_minutes, work_start, work_end)

    # Compute the intersection of free intervals among all participants
    # Start with Walter's free time since he is free all day.
    common_free = free_times["Walter"]
    for person in ["Cynthia", "Ann", "Catherine", "Kyle"]:
        common_free = intersect_intervals(common_free, free_times[person])

    # Find a common interval with at least the duration of the meeting.
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        meeting_start = minutes_to_time(meeting_slot[0])
        meeting_end = minutes_to_time(meeting_slot[1])
        # Output in the format: HH:MM:HH:MM along with the day of the week.
        print(f"{day} {meeting_start}:{meeting_end}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()