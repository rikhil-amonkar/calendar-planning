def main():
    # Meeting duration is 30 minutes, work hours: 9:00 (0 min) to 17:00 (480 min)
    # Represent busy times as half-open intervals [start, end) in minutes from 9:00
    busy_times = {
        "Katherine": [(180, 210), (240, 330)],  # 12:00-12:30, 13:00-14:30
        "Rebecca": [],  # Free all day
        "Julie": [(0, 30), (90, 120), (270, 300), (360, 390)],  # 9:00-9:30, 10:30-11:00, 13:30-14:00, 15:00-15:30
        "Angela": [(0, 60), (90, 120), (150, 300), (330, 360), (450, 480)],  # 9:00-10:00, 10:30-11:00, 11:30-14:00, 14:30-15:00, 16:30-17:00
        "Nicholas": [(30, 120), (150, 270), (300, 420), (450, 480)],  # 9:30-11:00, 11:30-13:30, 14:00-16:00, 16:30-17:00
        "Carl": [(0, 120), (150, 210), (240, 330), (360, 420), (450, 480)]  # 9:00-11:00, 11:30-12:30, 13:00-14:30, 15:00-16:00, 16:30-17:00
    }
    
    # Generate candidate start times (in minutes from 9:00): 0, 30, 60, ... 450 (16:30)
    all_starts = list(range(0, 451, 30))
    # Prioritize times after 15:00 (>=360 minutes)
    candidates_after_1500 = [s for s in all_starts if s >= 360]
    candidates_before_1500 = [s for s in all_starts if s < 360]
    
    # Check slots in prioritized order
    slot_found = None
    for candidate_list in [candidates_after_1500, candidates_before_1500]:
        for start in candidate_list:
            end = start + 30
            # Check if slot [start, end) is free for all participants
            free_slot = True
            for intervals in busy_times.values():
                for (busy_start, busy_end) in intervals:
                    # Check for overlap: [start, end) overlaps [busy_start, busy_end) if:
                    if start < busy_end and end > busy_start:
                        free_slot = False
                        break
                if not free_slot:
                    break
            if free_slot:
                slot_found = (start, end)
                break
        if slot_found:
            break
    
    # Convert slot to time strings
    def minutes_to_time(minutes):
        total_minutes = minutes
        hours = 9 + total_minutes // 60
        minutes_part = total_minutes % 60
        return f"{hours:02d}:{minutes_part:02d}"
    
    start_time_str = minutes_to_time(slot_found[0])
    end_time_str = minutes_to_time(slot_found[1])
    
    # Output day and time range in HH:MM:HH:MM format
    print("Monday")
    print(f"{start_time_str}:{end_time_str}")

if __name__ == "__main__":
    main()