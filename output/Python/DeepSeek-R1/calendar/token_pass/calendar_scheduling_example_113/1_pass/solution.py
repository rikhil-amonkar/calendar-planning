def main():
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    duration = 30
    
    # Busy intervals in minutes
    bradley_busy = [(570, 600), (750, 780), (810, 840), (930, 960)]
    teresa_busy = [(630, 660), (720, 750), (780, 810), (870, 900)]
    elizabeth_busy = [(540, 570), (630, 690), (780, 810), (870, 900), (930, 1020)]
    christian_busy = [(540, 570), (630, 1020)]
    
    participants_busy = [bradley_busy, teresa_busy, elizabeth_busy, christian_busy]
    
    # Check every 30-minute slot within work hours
    for start in range(work_start, work_end - duration + 1, 30):
        end = start + duration
        # Check if slot is within work hours
        if end > work_end:
            continue
            
        # Check availability for each participant
        slot_available = True
        for busy_intervals in participants_busy:
            person_available = True
            for busy_start, busy_end in busy_intervals:
                # Check for overlap
                if not (end <= busy_start or start >= busy_end):
                    person_available = False
                    break
            if not person_available:
                slot_available = False
                break
                
        if slot_available:
            # Convert minutes to HH:MM format
            start_hour = start // 60
            start_minute = start % 60
            end_hour = end // 60
            end_minute = end % 60
            
            print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
            return
            
    print("No suitable time found")

if __name__ == "__main__":
    main()