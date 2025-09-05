def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    busy_intervals.sort(key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(list1, list2):
    intersection = []
    for int1 in list1:
        for int2 in list2:
            start = max(int1[0], int2[0])
            end = min(int1[1], int2[1])
            if start < end:
                intersection.append((start, end))
    return intersection

def main():
    meeting_duration = 30  # in minutes
    # Define working hours (minutes from midnight)
    work_start = 9 * 60      # 09:00 -> 540 minutes
    work_end = 17 * 60       # 17:00 -> 1020 minutes

    # Busy intervals for each participant (in minutes)
    # Adam: 14:00 to 15:00 -> (840, 900)
    adam_busy = [(14 * 60, 15 * 60)]
    
    # John: 13:00-13:30, 14:00-14:30, 15:30-16:00, 16:30-17:00
    john_busy = [
        (13 * 60, 13 * 60 + 30),
        (14 * 60, 14 * 60 + 30),
        (15 * 60 + 30, 16 * 60),
        (16 * 60 + 30, 17 * 60)
    ]
    
    # Stephanie: 9:30-10:00, 10:30-11:00, 11:30-16:00, 16:30-17:00
    stephanie_busy = [
        (9 * 60 + 30, 10 * 60),
        (10 * 60 + 30, 11 * 60),
        (11 * 60 + 30, 16 * 60),
        (16 * 60 + 30, 17 * 60)
    ]
    
    # Anna: 9:30-10:00, 12:00-12:30, 13:00-15:30, 16:30-17:00
    anna_busy = [
        (9 * 60 + 30, 10 * 60),
        (12 * 60, 12 * 60 + 30),
        (13 * 60, 15 * 60 + 30),
        (16 * 60 + 30, 17 * 60)
    ]
    
    # Calculate free intervals for each participant
    adam_free = get_free_intervals(adam_busy, work_start, work_end)
    john_free = get_free_intervals(john_busy, work_start, work_end)
    stephanie_free = get_free_intervals(stephanie_busy, work_start, work_end)
    anna_free = get_free_intervals(anna_busy, work_start, work_end)

    # Anna's preference: do not meet before 14:30 (14*60+30 = 870 minutes)
    anna_pref = 14 * 60 + 30
    anna_free_adjusted = []
    for start, end in anna_free:
        new_start = max(start, anna_pref)
        if new_start < end:
            anna_free_adjusted.append((new_start, end))
    
    # Find common free intervals across all participants
    common_free = adam_free
    for free in [john_free, stephanie_free, anna_free_adjusted]:
        common_free = intersect_intervals(common_free, free)
    
    # Choose the earliest interval that can accommodate the meeting duration.
    meeting_slot = None
    for start, end in sorted(common_free, key=lambda x: x[0]):
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        start_str = minutes_to_time(meeting_slot[0])
        end_str = minutes_to_time(meeting_slot[1])
        # Output the final meeting time in the format HH:MM:HH:MM along with the day.
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()