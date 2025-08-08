def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def slot_conflicts(start, end, busy_intervals):
    # Check if the candidate meeting slot [start, end) overlaps with any busy interval.
    for b_start, b_end in busy_intervals:
        if start < b_end and end > b_start:
            return True
    return False

def main():
    # Meeting parameters
    meeting_duration = 30  # minutes
    working_start = 9 * 60   # 9:00 in minutes (540)
    working_end = 17 * 60    # 17:00 in minutes (1020)
    meeting_day = "Monday"
    
    # Busy schedules for each participant (times in minutes from midnight)
    schedules = {
        "Patrick": [(13*60 + 30, 14*60), (14*60 + 30, 15*60)],
        "Shirley": [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (14*60 + 30, 15*60), (16*60, 17*60)],
        "Jeffrey": [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (11*60 + 30, 12*60), (13*60, 13*60 + 30), (16*60, 17*60)],
        "Gloria": [(11*60 + 30, 12*60), (15*60, 15*60 + 30)],
        "Nathan": [(9*60, 9*60 + 30), (10*60 + 30, 12*60), (14*60, 17*60)],
        "Angela": [(9*60, 9*60 + 30), (10*60, 11*60), (12*60 + 30, 15*60), (15*60 + 30, 16*60 + 30)],
        "David": [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 14*60), (14*60 + 30, 16*60 + 30)]
    }
    
    # Combine all busy intervals from all participants
    all_busy_intervals = []
    for busy in schedules.values():
        all_busy_intervals.extend(busy)
    
    # Search over the workday for a free 30-minute slot
    available_slot = None
    for start in range(working_start, working_end - meeting_duration + 1):
        end = start + meeting_duration
        if not slot_conflicts(start, end, all_busy_intervals):
            available_slot = (start, end)
            break

    # Output the result in the format "HH:MM:HH:MM" with the day of the week.
    if available_slot:
        start_str = time_to_str(available_slot[0])
        end_str = time_to_str(available_slot[1])
        print(f"{meeting_day} {start_str}:{end_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()