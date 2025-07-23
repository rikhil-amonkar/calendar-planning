def main():
    # Define work hours in minutes (9:00 to 17:00)
    work_start = 9 * 60   # 540 minutes
    work_end = 17 * 60    # 1020 minutes
    meeting_duration = 30  # minutes

    # Busy intervals for each participant per day, represented in minutes
    cheryl_busy = {
        'Monday': [(9*60, 9*60+30), (11*60+30, 13*60), (15*60+30, 16*60)],
        'Tuesday': [(15*60, 15*60+30)],
        'Wednesday': []  # Cheryl cannot meet, so we skip this day
    }
    
    kyle_busy = {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60+30, 17*60)],
        'Wednesday': []  # Not considered
    }
    
    days_to_check = ['Monday', 'Tuesday']  # Wednesday excluded per Cheryl's constraint

    # Function to merge overlapping intervals
    def merge_intervals(intervals):
        if not intervals:
            return []
        sorted_intervals = sorted(intervals, key=lambda x: x[0])
        merged = []
        start, end = sorted_intervals[0]
        for interval in sorted_intervals[1:]:
            if interval[0] <= end:
                end = max(end, interval[1])
            else:
                merged.append((start, end))
                start, end = interval
        merged.append((start, end))
        return merged

    # Function to get free intervals from busy intervals within work hours
    def get_free_intervals(busy_intervals, start_bound, end_bound):
        merged_busy = merge_intervals(busy_intervals)
        free_intervals = []
        current = start_bound
        
        for busy_start, busy_end in merged_busy:
            if current < busy_start:
                free_intervals.append((current, busy_start))
            current = max(current, busy_end)
        
        if current < end_bound:
            free_intervals.append((current, end_bound))
            
        return free_intervals

    # Function to find overlapping intervals between two sets
    def find_common_intervals(intervals1, intervals2):
        common = []
        i = j = 0
        while i < len(intervals1) and j < len(intervals2):
            start1, end1 = intervals1[i]
            start2, end2 = intervals2[j]
            
            low = max(start1, start2)
            high = min(end1, end2)
            
            if low < high:
                common.append((low, high))
            
            if end1 < end2:
                i += 1
            else:
                j += 1
        return common

    # Convert minutes to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Iterate over days to find the first available slot
    for day in days_to_check:
        cheryl_free = get_free_intervals(cheryl_busy[day], work_start, work_end)
        kyle_free = get_free_intervals(kyle_busy[day], work_start, work_end)
        common_free = find_common_intervals(cheryl_free, kyle_free)
        
        for start, end in common_free:
            duration = end - start
            if duration >= meeting_duration:
                # Use the earliest possible slot within the interval
                meeting_end = start + meeting_duration
                start_str = minutes_to_time(start)
                end_str = minutes_to_time(meeting_end)
                print(f"{day}")
                print(f"{start_str}:{end_str}")
                return

    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()