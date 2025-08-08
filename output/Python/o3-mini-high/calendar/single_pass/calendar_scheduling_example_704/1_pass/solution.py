def minutes_to_hhmm(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_slot(busy_intervals, work_start, work_end, duration):
    """Find earliest free slot (in minutes) of at least 'duration' length between work_start and work_end."""
    busy_merged = merge_intervals(busy_intervals)
    free_slots = []
    
    # Gap before first meeting.
    if not busy_merged:
        free_slots.append((work_start, work_end))
    else:
        if busy_merged[0][0] > work_start:
            free_slots.append((work_start, busy_merged[0][0]))
        # Gaps between busy intervals.
        for i in range(len(busy_merged) - 1):
            start = busy_merged[i][1]
            end = busy_merged[i+1][0]
            if end - start > 0:
                free_slots.append((start, end))
        # Gap after last meeting.
        if busy_merged[-1][1] < work_end:
            free_slots.append((busy_merged[-1][1], work_end))
    
    # Return the earliest free slot that fits the meeting duration.
    for start, end in free_slots:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    meeting_duration = 30  # meeting length in minutes
    work_start = 9 * 60    # 9:00 in minutes
    work_end = 17 * 60     # 17:00 in minutes
    
    # Define each participant's busy intervals (in minutes) for each day.
    # Note: Although Larry is free all week, his preference is to avoid Wednesday.
    # Samuel's intervals are provided below.
    calendars = {
        "Monday": {
            "Larry": [],
            "Samuel": [
                (10*60 + 30, 11*60),     # 10:30-11:00
                (12*60, 12*60 + 30),      # 12:00-12:30
                (13*60, 15*60),           # 13:00-15:00
                (15*60 + 30, 16*60 + 30)   # 15:30-16:30
            ]
        },
        "Tuesday": {
            "Larry": [],
            "Samuel": [
                (9*60, 12*60),           # 9:00-12:00
                (14*60, 15*60 + 30),       # 14:00-15:30
                (16*60 + 30, 17*60)        # 16:30-17:00
            ]
        },
        "Wednesday": {
            "Larry": [],
            "Samuel": [
                (10*60 + 30, 11*60),      # 10:30-11:00
                (11*60 + 30, 12*60),      # 11:30-12:00
                (12*60 + 30, 13*60),      # 12:30-13:00
                (14*60, 14*60 + 30),      # 14:00-14:30
                (15*60, 16*60)           # 15:00-16:00
            ]
        }
    }
    
    # Preference order:
    # - Monday is best.
    # - Tuesday is less ideal for Samuel.
    # - Wednesday should be avoided by Larry if possible.
    # So we check in the following order.
    preferred_days = ["Monday", "Tuesday", "Wednesday"]
    
    for day in preferred_days:
        busy_intervals = []
        # Combine busy intervals for all participants on this day.
        # (Larry is completely free so it’s just Samuel’s busy times.)
        for person in calendars[day]:
            busy_intervals.extend(calendars[day][person])
        
        slot = get_free_slot(busy_intervals, work_start, work_end, meeting_duration)
        if slot:
            start, end = slot
            # Output in the format: Day {HH:MM:HH:MM}
            print(f"{day} {{{minutes_to_hhmm(start)}:{minutes_to_hhmm(end)}}}")
            break

if __name__ == "__main__":
    main()