def main():
    # Meeting duration in minutes
    meeting_duration = 30
    work_start = 0  # 9:00 in minutes from 9:00
    work_end = 480  # 17:00 in minutes from 9:00

    # Define busy intervals for each day for Susan and Sandra in minutes from 9:00
    busy_intervals = {
        'Monday': {
            'Susan': [(210, 240), (270, 300)],
            'Sandra': [(0, 240), (300, 360), (420, 480)]  # includes constraint after 16:00
        },
        'Tuesday': {
            'Susan': [(150, 180)],
            'Sandra': [(0, 30), (90, 180), (210, 270), (300, 330), (420, 480)]
        },
        'Wednesday': {
            'Susan': [(30, 90), (300, 330), (390, 450)],
            'Sandra': [(0, 150), (180, 210), (240, 480)]
        }
    }

    # Day order to check: Monday first, then Wednesday, then Tuesday (due to preference)
    days_to_check = ['Monday', 'Wednesday', 'Tuesday']

    # Function to get free intervals from busy intervals
    def get_free_intervals(busy_list, start_time, end_time):
        if not busy_list:
            return [(start_time, end_time)]
        busy_list.sort(key=lambda x: x[0])
        free_intervals = []
        current_time = start_time
        for busy in busy_list:
            if current_time < busy[0]:
                free_intervals.append((current_time, busy[0]))
            current_time = max(current_time, busy[1])
        if current_time < end_time:
            free_intervals.append((current_time, end_time))
        return free_intervals

    # Function to find common free intervals between two sets of free intervals
    def get_common_free_intervals(free1, free2):
        common = []
        i = j = 0
        while i < len(free1) and j < len(free2):
            start1, end1 = free1[i]
            start2, end2 = free2[j]
            start_max = max(start1, start2)
            end_min = min(end1, end2)
            if start_max < end_min:
                common.append((start_max, end_min))
            if end1 < end2:
                i += 1
            else:
                j += 1
        return common

    # Function to convert minutes to HH:MM string
    def min_to_time(minutes):
        hour = 9 + minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Iterate through days in preferred order
    for day in days_to_check:
        busy_susan = busy_intervals[day]['Susan']
        busy_sandra = busy_intervals[day]['Sandra']
        
        free_susan = get_free_intervals(busy_susan, work_start, work_end)
        free_sandra = get_free_intervals(busy_sandra, work_start, work_end)
        
        common_free = get_common_free_intervals(free_susan, free_sandra)
        
        for start, end in common_free:
            duration = end - start
            if duration >= meeting_duration:
                start_time_str = min_to_time(start)
                end_time_str = min_to_time(start + meeting_duration)  # meeting ends at start + duration
                print(f"{day} {start_time_str}:{end_time_str}")
                return

    # If no slot found, but problem states there is a solution, so this should not happen
    print("No suitable time found")

if __name__ == "__main__":
    main()