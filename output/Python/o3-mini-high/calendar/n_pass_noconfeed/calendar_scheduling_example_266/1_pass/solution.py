def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def merge_intervals(intervals):
    # Sort intervals by their start time
    intervals.sort(key=lambda x: x[0])
    merged = []
    for interval in intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            # If intervals overlap or are adjacent, merge them
            if current_start <= last_end:
                merged[-1] = (last_start, max(last_end, current_end))
            else:
                merged.append(interval)
    return merged

def main():
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Work hours (in minutes from midnight)
    work_start = 9 * 60   # 9:00 -> 540 minutes
    work_end = 17 * 60    # 17:00 -> 1020 minutes

    # Busy intervals for each participant (in minutes)
    participants_busy = {
        "Joe": [(9*60+30, 10*60), (10*60+30, 11*60)],           # 9:30-10:00, 10:30-11:00
        "Keith": [(11*60+30, 12*60), (15*60, 15*60+30)],         # 11:30-12:00, 15:00-15:30
        "Patricia": [(9*60, 9*60+30), (13*60, 13*60+30)],         # 9:00-9:30, 13:00-13:30
        "Nancy": [(9*60, 11*60), (11*60+30, 16*60+30)],           # 9:00-11:00, 11:30-16:30
        "Pamela": [
            (9*60, 10*60), (10*60+30, 11*60),
            (11*60+30, 12*60+30), (13*60, 14*60),
            (14*60+30, 15*60), (15*60+30, 16*60),
            (16*60+30, 17*60)
        ]
    }
    
    # Combine all busy intervals from all participants
    all_busy = []
    for intervals in participants_busy.values():
        all_busy.extend(intervals)
    
    # Merge overlapping busy intervals
    merged_busy = merge_intervals(all_busy)
    
    # Find free intervals within work hours
    free_intervals = []
    if merged_busy:
        # Check for free slot before the first busy block
        if work_start < merged_busy[0][0]:
            free_intervals.append((work_start, merged_busy[0][0]))
        # Check gaps between merged busy intervals
        for i in range(len(merged_busy) - 1):
            gap_start = merged_busy[i][1]
            gap_end = merged_busy[i+1][0]
            free_intervals.append((gap_start, gap_end))
        # Check for free slot after the last busy block
        if merged_busy[-1][1] < work_end:
            free_intervals.append((merged_busy[-1][1], work_end))
    else:
        free_intervals.append((work_start, work_end))
    
    # Find the first free interval that can accommodate the meeting
    meeting_slot = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    # Print the meeting time in the required format
    if meeting_slot:
        start_str = minutes_to_time_str(meeting_slot[0])
        end_str = minutes_to_time_str(meeting_slot[1])
        # The meeting is scheduled on Monday.
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()