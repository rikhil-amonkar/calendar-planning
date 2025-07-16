def time_str_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    current_start, current_end = sorted_intervals[0]
    for s, e in sorted_intervals[1:]:
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))
    return merged

def invert_intervals(work_start, work_end, busy_intervals):
    merged_busy = merge_intervals(busy_intervals)
    free = []
    if not merged_busy:
        return [(work_start, work_end)]
    if work_start < merged_busy[0][0]:
        free.append((work_start, merged_busy[0][0]))
    for i in range(1, len(merged_busy)):
        free.append((merged_busy[i-1][1], merged_busy[i][0]))
    if merged_busy[-1][1] < work_end:
        free.append((merged_busy[-1][1], work_end))
    return free

def find_common_free_intervals(free1, free2):
    common_free = []
    i = j = 0
    while i < len(free1) and j < len(free2):
        start = max(free1[i][0], free2[j][0])
        end = min(free1[i][1], free2[j][1])
        if start < end:
            common_free.append((start, end))
        if free1[i][1] < free2[j][1]:
            i += 1
        else:
            j += 1
    return common_free

def main():
    work_start_min = time_str_to_minutes("9:00")
    work_end_min = time_str_to_minutes("17:00")
    meeting_duration = 60  # minutes
    
    # Define the schedule
    schedule = {
        'Martha': {
            'Monday': [("16:00", "17:00")],
            'Tuesday': [("15:00", "15:30")],
            'Wednesday': [("10:00", "11:00"), ("14:00", "14:30")]
        },
        'Beverly': {
            'Monday': [("9:00", "13:30"), ("14:00", "17:00")],
            'Tuesday': [("9:00", "17:00")],
            'Wednesday': [("9:30", "15:30"), ("16:30", "17:00")]
        }
    }
    
    days = ["Monday", "Tuesday", "Wednesday"]
    
    for day in days:
        # Get busy intervals for Martha and convert to minutes
        martha_busy = []
        for interval in schedule['Martha'][day]:
            start_min = time_str_to_minutes(interval[0])
            end_min = time_str_to_minutes(interval[1])
            martha_busy.append((start_min, end_min))
        
        # Get busy intervals for Beverly and convert to minutes
        beverly_busy = []
        for interval in schedule['Beverly'][day]:
            start_min = time_str_to_minutes(interval[0])
            end_min = time_str_to_minutes(interval[1])
            beverly_busy.append((start_min, end_min))
        
        # Calculate free intervals for each
        martha_free = invert_intervals(work_start_min, work_end_min, martha_busy)
        beverly_free = invert_intervals(work_start_min, work_end_min, beverly_busy)
        
        # Find common free intervals
        common_free = find_common_free_intervals(martha_free, beverly_free)
        
        # Check for a slot that fits the meeting duration
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                start_str = minutes_to_time_str(meeting_start)
                end_str = minutes_to_time_str(meeting_end)
                print(f"{day}:{start_str}:{end_str}")
                return
    
    # If no slot is found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()