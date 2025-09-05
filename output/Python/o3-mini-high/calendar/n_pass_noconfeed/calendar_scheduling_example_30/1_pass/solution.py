def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def invert_busy(work_start, work_end, busy_list):
    free = []
    current = work_start
    for b_start, b_end in busy_list:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            result.append((start, end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

def intersect_all(lists):
    common = lists[0]
    for l in lists[1:]:
        common = intersect_intervals(common, l)
    return common

def main():
    # Meeting duration: 30 minutes
    meeting_duration = 30
    
    # Working hours (in minutes from midnight)
    work_start = 9 * 60    # 09:00 --> 540
    work_end   = 17 * 60   # 17:00 --> 1020

    # Busy schedules in minutes for Monday:
    # Jeffrey: 9:30-10:00, 10:30-11:00
    jeffrey_busy = [(9*60+30, 10*60), (10*60+30, 11*60)]
    # Virginia: 9:00-9:30, 10:00-10:30, 14:30-15:00, 16:00-16:30
    virginia_busy = [(9*60, 9*60+30), (10*60, 10*60+30),
                     (14*60+30, 15*60), (16*60, 16*60+30)]
    # Melissa: 9:00-11:30, 12:00-12:30, 13:00-15:00, 16:00-17:00
    melissa_busy = [(9*60, 11*60+30), (12*60, 12*60+30),
                    (13*60, 15*60), (16*60, 17*60)]
    
    # Compute free intervals for each participant within working hours
    jeffrey_free = invert_busy(work_start, work_end, jeffrey_busy)
    virginia_free = invert_busy(work_start, work_end, virginia_busy)
    melissa_free_full = invert_busy(work_start, work_end, melissa_busy)
    
    # Apply Melissa's preference: she would rather not meet after 14:00.
    # For any free interval that stretches beyond 14:00 (840 minutes), limit it to 14:00.
    melissa_free = []
    for start, end in melissa_free_full:
        if start < 14 * 60:
            melissa_free.append((start, min(end, 14 * 60)))
    
    # Find the common free intervals across all participants
    common_free = intersect_all([jeffrey_free, virginia_free, melissa_free])
    
    # Pick the earliest interval of at least meeting_duration minutes
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        start_str = minutes_to_str(meeting_slot[0])
        end_str = minutes_to_str(meeting_slot[1])
        print(f"Monday, {start_str}:{end_str}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()