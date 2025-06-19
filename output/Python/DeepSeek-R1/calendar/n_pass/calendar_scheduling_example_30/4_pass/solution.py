def main(input_data):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    meeting_duration = 30
    work_start = 0
    work_end = 480  # 17:00 in minutes from 9:00 (which is 480 minutes)

    def convert_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        total_minutes = hours * 60 + minutes
        return total_minutes - 540  # 9:00 is 540 minutes from midnight

    def convert_to_time(minutes):
        total_minutes_since_midnight = 540 + minutes
        hours = total_minutes_since_midnight // 60
        mins = total_minutes_since_midnight % 60
        return f"{hours:02d}:{mins:02d}"

    for day in days:
        if day not in input_data:
            continue
            
        jeffrey = input_data[day]["jeffrey"]
        virginia = input_data[day]["virginia"]
        melissa = input_data[day]["melissa"]
        
        all_busy = []
        
        for interval in jeffrey:
            start_min = convert_to_minutes(interval[0])
            end_min = convert_to_minutes(interval[1])
            all_busy.append((start_min, end_min))
            
        for interval in virginia:
            start_min = convert_to_minutes(interval[0])
            end_min = convert_to_minutes(interval[1])
            all_busy.append((start_min, end_min))
            
        for interval in melissa:
            start_min = convert_to_minutes(interval[0])
            end_min = convert_to_minutes(interval[1])
            all_busy.append((start_min, end_min))
        
        if not all_busy:
            start_str = convert_to_time(0)
            end_str = convert_to_time(meeting_duration)
            print(day)
            print(f"{start_str} {end_str}")
            return
        
        all_busy.sort(key=lambda x: x[0])
        
        merged = []
        current_start, current_end = all_busy[0]
        for i in range(1, len(all_busy)):
            s, e = all_busy[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
        
        free_intervals = []
        current_time = work_start
        for start_int, end_int in merged:
            if current_time < start_int:
                gap_start = current_time
                gap_end = start_int
                if gap_end - gap_start >= meeting_duration:
                    free_intervals.append((gap_start, gap_end))
                current_time = end_int
            else:
                if end_int > current_time:
                    current_time = end_int
        if current_time < work_end:
            gap_start = current_time
            gap_end = work_end
            if gap_end - gap_start >= meeting_duration:
                free_intervals.append((gap_start, gap_end))
        
        candidate = None
        for start_free, end_free in free_intervals:
            slot_end = start_free + meeting_duration
            if slot_end <= end_free and slot_end <= 300:  # 300 minutes from 9:00 is 14:00
                candidate = (start_free, slot_end)
                break
                
        if candidate is None:
            for start_free, end_free in free_intervals:
                slot_end = start_free + meeting_duration
                if slot_end <= end_free:
                    candidate = (start_free, slot_end)
                    break
                    
        if candidate is not None:
            start_time_str = convert_to_time(candidate[0])
            end_time_str = convert_to_time(candidate[1])
            print(day)
            print(f"{start_time_str} {end_time_str}")
            return
            
    print("No meeting possible")

if __name__ == "__main__":
    input_data = {}
    days_order = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    for day in days_order:
        data_line = input().split()
        n_jeffrey = int(data_line[1])
        n_virginia = int(data_line[2])
        n_melissa = int(data_line[3])
        jeffrey_list = []
        for i in range(n_jeffrey):
            times = input().split()
            jeffrey_list.append([times[0], times[1]])
        virginia_list = []
        for i in range(n_virginia):
            times = input().split()
            virginia_list.append([times[0], times[1]])
        melissa_list = []
        for i in range(n_melissa):
            times = input().split()
            melissa_list.append([times[0], times[1]])
        input_data[day] = {
            "jeffrey": jeffrey_list,
            "virginia": virginia_list,
            "melissa": melissa_list
        }
    
    main(input_data)