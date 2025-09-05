def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def compute_free_intervals(busy, work_start, work_end):
    # Make sure busy intervals are sorted by start time
    busy_sorted = sorted(busy, key=lambda x: x[0])
    free = []
    current = work_start
    for b_start, b_end in busy_sorted:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2, duration):
    common = []
    for int1 in list1:
        for int2 in list2:
            start = max(int1[0], int2[0])
            end = min(int1[1], int2[1])
            if end - start >= duration:
                common.append((start, end))
    return common

def main():
    meeting_duration = 30  # minutes
    work_start = 9 * 60    # 09:00 in minutes (540)
    work_end = 17 * 60     # 17:00 in minutes (1020)

    # Define busy schedules for each person on each day (times in minutes)
    schedules = {
        "Monday": {
            "Joshua": [(15 * 60, 15 * 60 + 30)],  # 15:00-15:30
            "Joyce": [
                (9 * 60, 9 * 60 + 30),            # 09:00-09:30
                (10 * 60, 11 * 60),               # 10:00-11:00
                (11 * 60 + 30, 12 * 60 + 30),     # 11:30-12:30
                (13 * 60, 15 * 60),               # 13:00-15:00
                (15 * 60 + 30, 17 * 60)           # 15:30-17:00
            ]
        },
        "Tuesday": {
            "Joshua": [
                (11 * 60 + 30, 12 * 60),          # 11:30-12:00
                (13 * 60, 13 * 60 + 30),          # 13:00-13:30
                (14 * 60 + 30, 15 * 60)           # 14:30-15:00
            ],
            "Joyce": [
                (9 * 60, 17 * 60)                 # 09:00-17:00 (busy all day)
            ]
        },
        "Wednesday": {
            "Joshua": [],  # No meetings scheduled
            "Joyce": [
                (9 * 60, 9 * 60 + 30),            # 09:00-09:30
                (10 * 60, 11 * 60),               # 10:00-11:00
                (12 * 60 + 30, 15 * 60 + 30),     # 12:30-15:30
                (16 * 60, 16 * 60 + 30)           # 16:00-16:30
            ]
        }
    }
    
    # The meeting can be scheduled on Monday, Tuesday or Wednesday.
    # Additional constraint: If the meeting is on Monday, it must not start before 12:00 (720 minutes).
    chosen_day = None
    meeting_start = None
    meeting_end = None

    for day in ["Monday", "Tuesday", "Wednesday"]:
        busy_joshua = schedules[day]["Joshua"]
        busy_joyce = schedules[day]["Joyce"]

        free_joshua = compute_free_intervals(busy_joshua, work_start, work_end)
        free_joyce = compute_free_intervals(busy_joyce, work_start, work_end)
        common_intervals = intersect_intervals(free_joshua, free_joyce, meeting_duration)

        # On Monday, adjust intervals so that the meeting does not start before 12:00.
        if day == "Monday":
            adjusted = []
            for interval in common_intervals:
                start, end = interval
                # If the interval starts before 12:00, shift the start to 12:00.
                if start < 12 * 60:
                    start = 12 * 60
                if end - start >= meeting_duration:
                    adjusted.append((start, end))
            common_intervals = adjusted

        # Choose the earliest available time slot in the common free intervals.
        if common_intervals:
            common_intervals.sort(key=lambda x: x[0])
            meeting_start = common_intervals[0][0]
            meeting_end = meeting_start + meeting_duration
            chosen_day = day
            break

    if chosen_day is not None:
        # Format the meeting time as HH:MM:HH:MM and output along with the day
        print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} {chosen_day}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()