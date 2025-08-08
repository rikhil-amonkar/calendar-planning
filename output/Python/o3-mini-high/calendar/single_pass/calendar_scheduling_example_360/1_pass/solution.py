def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy, work_start, work_end):
    free = []
    current = work_start
    # Sort busy intervals by start time
    for interval in sorted(busy, key=lambda x: x[0]):
        if interval[0] > current:
            free.append((current, interval[0]))
        current = max(current, interval[1])
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    result = []
    for int1 in intervals1:
        for int2 in intervals2:
            start = max(int1[0], int2[0])
            end = min(int1[1], int2[1])
            if end - start > 0:
                result.append((start, end))
    return result

def main():
    # Define working hours in minutes since midnight: 9:00 = 540, 17:00 = 1020.
    work_start = 540
    work_end = 1020
    meeting_duration = 30  # in minutes

    # Busy schedules (in minutes) for each participant on Monday:
    schedules = {
        "Emily": [(600, 630), (960, 990)],              # 10:00-10:30 and 16:00-16:30
        "Mason": [],                                   # free entire day
        "Maria": [(630, 660), (840, 870)],              # 10:30-11:00 and 14:00-14:30
        "Carl": [(570, 600), (630, 750), (810, 840), (870, 930), (960, 1020)],
        "David": [(570, 660), (690, 720), (750, 810), (840, 900), (960, 1020)],
        "Frank": [(570, 630), (660, 690), (750, 810), (870, 1020)]
    }

    # Compute free intervals for each participant
    free_intervals = {}
    for person, busy in schedules.items():
        free_intervals[person] = get_free_intervals(busy, work_start, work_end)

    # Compute the common free intervals by intersecting everyone's free intervals
    participants = list(schedules.keys())
    common_free = free_intervals[participants[0]]
    for person in participants[1:]:
        common_free = intersect_intervals(common_free, free_intervals[person])

    # Find the first common interval that can accommodate the meeting
    meeting_slot = None
    for interval in sorted(common_free, key=lambda x: x[0]):
        if interval[1] - interval[0] >= meeting_duration:
            meeting_slot = (interval[0], interval[0] + meeting_duration)
            break

    if meeting_slot:
        start_str = minutes_to_time(meeting_slot[0])
        end_str = minutes_to_time(meeting_slot[1])
        day = "Monday"
        # Output in the required format: HH:MM:HH:MM along with the day of the week.
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()