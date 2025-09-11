def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60
    work_end = 17 * 60

    # Meeting duration in minutes
    duration = 30

    # Harold's constraint: meeting must end by 13:00 (780 minutes)
    harold_end_constraint = 13 * 60

    # Busy intervals in minutes (since midnight)
    busy_times = {
        'Jacqueline': [(9*60, 9*60+30), (11*60, 11*60+30), (12*60+30, 13*60), (15*60+30, 16*60)],
        'Harold': [(10*60, 10*60+30), (13*60, 13*60+30), (15*60, 17*60)],
        'Arthur': [(9*60, 9*60+30), (10*60, 12*60+30), (14*60+30, 15*60), (15*60+30, 17*60)],
        'Kelly': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60+30), (14*60, 15*60), (15*60+30, 16*60)]
    }

    # Find available slot between 9:00 and 13:00 considering Harold's constraint
    for start_minute in range(work_start, harold_end_constraint - duration + 1, 30):
        end_minute = start_minute + duration
        # Check if slot fits Harold's end constraint
        if end_minute > harold_end_constraint:
            continue
            
        # Check availability for all participants
        all_available = True
        for person, intervals in busy_times.items():
            for busy_start, busy_end in intervals:
                # Check for overlap with busy interval
                if not (end_minute <= busy_start or start_minute >= busy_end):
                    all_available = False
                    break
            if not all_available:
                break
                
        if all_available:
            # Format the time as HH:MM
            start_time = f"{start_minute // 60:02d}:{start_minute % 60:02d}"
            end_time = f"{end_minute // 60:02d}:{end_minute % 60:02d}"
            print(f"Monday {start_time}:{end_time}")
            return
            
    print("No suitable time found")

if __name__ == "__main__":
    main()