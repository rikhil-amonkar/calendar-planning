def get_free_intervals(work_start, work_end, busy_list):
    free = [(work_start, work_end)]
    for busy in busy_list:
        new_free = []
        for interval in free:
            # If the free interval doesn't overlap with the busy interval, keep it
            if interval[1] <= busy[0] or interval[0] >= busy[1]:
                new_free.append(interval)
            else:
                # If there's overlap, split the free interval around the busy one
                if interval[0] < busy[0]:
                    new_free.append((interval[0], busy[0]))
                if interval[1] > busy[1]:
                    new_free.append((busy[1], interval[1]))
        free = new_free
    return free

def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes
    duration = 30     # meeting duration in minutes

    # Busy intervals in minutes for each day and person
    cheryl_busy = {
        'Monday': [(540, 570), (690, 780), (930, 960)],
        'Tuesday': [(900, 930)],
    }
    kyle_busy = {
        'Monday': [(540, 1020)],
        'Tuesday': [(570, 1020)],
    }
    
    days = ['Monday', 'Tuesday']  # Wednesday excluded as Cheryl cannot meet
    
    for day in days:
        # Get free intervals for Cheryl and Kyle
        cheryl_free = get_free_intervals(work_start, work_end, cheryl_busy[day])
        kyle_free = get_free_intervals(work_start, work_end, kyle_busy[day])
        
        # Find common free intervals
        common_free = []
        for c_interval in cheryl_free:
            for k_interval in kyle_free:
                start = max(c_interval[0], k_interval[0])
                end = min(c_interval[1], k_interval[1])
                if start < end:  # valid interval
                    common_free.append((start, end))
        
        # Sort common intervals by start time
        common_free.sort(key=lambda x: x[0])
        
        # Check each common interval for sufficient duration
        for interval in common_free:
            if interval[1] - interval[0] >= duration:
                start_minutes = interval[0]
                end_minutes = start_minutes + duration
                
                # Convert start and end to HH:MM format
                start_hour = start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = end_minutes // 60
                end_minute = end_minutes % 60
                
                time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                print(day)
                print(time_str)
                return
    
    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()