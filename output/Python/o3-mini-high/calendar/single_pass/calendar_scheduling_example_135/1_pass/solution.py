def get_free_intervals(working_start, working_end, busy_intervals):
    free_intervals = []
    current = working_start
    # Sort the busy intervals by start time
    for busy in sorted(busy_intervals, key=lambda x: x[0]):
        if busy[0] > current:
            free_intervals.append((current, busy[0]))
        current = max(current, busy[1])
    if current < working_end:
        free_intervals.append((current, working_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    intersection = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                intersection.append((start, end))
    return intersection

def minutes_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def find_common_slot(working_start, working_end, participants_busy, meeting_duration):
    # Calculate free intervals for every participant.
    all_free = []
    for busy in participants_busy:
        free = get_free_intervals(working_start, working_end, busy)
        all_free.append(free)
        
    # Start with the free intervals of the first participant.
    common = all_free[0]
    for free in all_free[1:]:
        common = intersect_intervals(common, free)
        
    # Find the first common interval that can accommodate the meeting.
    for interval in common:
        if interval[1] - interval[0] >= meeting_duration:
            return interval[0], interval[0] + meeting_duration
    return None

def main():
    meeting_duration = 30  # in minutes
    # Define work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
    working_start = 9 * 60
    working_end = 17 * 60
    day = "Monday"
    
    # Define busy intervals for each participant as tuples of (start, end) in minutes.
    # Eric: no meetings.
    eric_busy = []
    
    # Ashley is busy during: 10:00-10:30, 11:00-12:00, 12:30-13:00, 15:00-16:00.
    ashley_busy = [
        (10 * 60, 10 * 60 + 30),
        (11 * 60, 12 * 60),
        (12 * 60 + 30, 13 * 60),
        (15 * 60, 16 * 60)
    ]
    
    # Ronald is busy during: 9:00-9:30, 10:00-11:30, 12:30-14:00, 14:30-17:00.
    ronald_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 14 * 60),
        (14 * 60 + 30, 17 * 60)
    ]
    
    # Larry is busy during: 9:00-12:00, 13:00-17:00.
    larry_busy = [
        (9 * 60, 12 * 60),
        (13 * 60, 17 * 60)
    ]
    
    participants_busy = [eric_busy, ashley_busy, ronald_busy, larry_busy]
    slot = find_common_slot(working_start, working_end, participants_busy, meeting_duration)
    
    if slot:
        start_str = minutes_to_str(slot[0])
        end_str = minutes_to_str(slot[1])
        # Output in the format HH:MM:HH:MM along with the day of the week.
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()