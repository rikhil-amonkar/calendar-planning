def main():
    day = "Monday"
    
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])
    
    emily_busy = [
        [time_to_minutes("10:00"), time_to_minutes("10:30")],
        [time_to_minutes("11:30"), time_to_minutes("12:30")],
        [time_to_minutes("14:00"), time_to_minutes("15:00")],
        [time_to_minutes("16:00"), time_to_minutes("16:30")]
    ]
    
    melissa_busy = [
        [time_to_minutes("9:30"), time_to_minutes("10:00")],
        [time_to_minutes("14:30"), time_to_minutes("15:00")]
    ]
    
    frank_busy = [
        [time_to_minutes("10:00"), time_to_minutes("10:30")],
        [time_to_minutes("11:00"), time_to_minutes("11:30")],
        [time_to_minutes("12:30"), time_to_minutes("13:00")],
        [time_to_minutes("13:30"), time_to_minutes("14:30")],
        [time_to_minutes("15:00"), time_to_minutes("16:00")],
        [time_to_minutes("16:30"), time_to_minutes("17:00")]
    ]
    
    constraint_start = time_to_minutes("9:00")
    constraint_end = time_to_minutes("9:30")
    
    def is_free(intervals, start, end):
        for busy_start, busy_end in intervals:
            if end > busy_start and start < busy_end:
                return False
        return True
    
    if (is_free(emily_busy, constraint_start, constraint_end) and
        is_free(melissa_busy, constraint_start, constraint_end) and
        is_free(frank_busy, constraint_start, constraint_end)):
        def minutes_to_time(mins):
            hours = mins // 60
            minutes = mins % 60
            return f"{hours:02d}:{minutes:02d}"
        
        start_str = minutes_to_time(constraint_start)
        end_str = minutes_to_time(constraint_end)
        print(day)
        print(f"{start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()