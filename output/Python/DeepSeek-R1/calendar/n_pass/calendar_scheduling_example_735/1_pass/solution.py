def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def main():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    meeting_duration = 30  # minutes

    # Define schedules using given constraints
    ronald_schedule = {
        'Monday': [('10:30', '11:00'), ('12:00', '12:30'), ('15:30', '16:00')],
        'Tuesday': [('9:00', '9:30'), ('12:00', '12:30'), ('15:30', '16:30')],
        'Wednesday': [('9:30', '10:30'), ('11:00', '12:00'), ('12:30', '13:00'), ('13:30', '14:00'), ('16:30', '17:00')]
    }
    amber_schedule = {
        'Monday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:30', '12:00'), ('12:30', '14:00'), ('14:30', '15:00'), ('15:30', '17:00')],
        'Tuesday': [('9:00', '9:30'), ('10:00', '11:30'), ('12:00', '12:30'), ('13:30', '15:30'), ('16:30', '17:00')],
        'Wednesday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:00', '13:30'), ('15:00', '15:30')]
    }

    days = ['Monday', 'Tuesday', 'Wednesday']
    for day in days:
        # Process Ronald's blocks for the day
        ronald_blocks = []
        for interval in ronald_schedule[day]:
            s, e = interval
            start_min = time_to_minutes(s)
            end_min = time_to_minutes(e)
            ronald_blocks.append((start_min, end_min))
        
        # Process Amber's blocks for the day
        amber_blocks = []
        for interval in amber_schedule[day]:
            s, e = interval
            start_min = time_to_minutes(s)
            end_min = time_to_minutes(e)
            amber_blocks.append((start_min, end_min))
        
        # Combine and sort intervals
        combined = ronald_blocks + amber_blocks
        combined.sort(key=lambda x: x[0])
        
        # Merge overlapping or adjacent intervals
        merged = []
        for interval in combined:
            if not merged:
                merged.append(interval)
            else:
                last_start, last_end = merged[-1]
                current_start, current_end = interval
                if current_start <= last_end:
                    merged[-1] = (last_start, max(last_end, current_end))
                else:
                    merged.append(interval)
        
        # Find free intervals within work hours
        free_intervals = []
        current_start = work_start
        for start, end in merged:
            if start > current_start:
                free_intervals.append((current_start, start))
            current_start = max(current_start, end)
        if current_start < work_end:
            free_intervals.append((current_start, work_end))
        
        # Check for the first free interval that fits the meeting
        for start, end in free_intervals:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                # Format start and end times
                start_hr, start_min = divmod(meeting_start, 60)
                end_hr, end_min = divmod(meeting_end, 60)
                print(f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}")
                print(day)
                return
    
    # Fallback if no slot found (should not occur per problem)
    print("No slot found")

if __name__ == "__main__":
    main()