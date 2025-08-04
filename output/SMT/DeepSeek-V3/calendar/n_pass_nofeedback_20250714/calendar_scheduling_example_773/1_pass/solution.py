from z3 import *

def solve_scheduling():
    # Define the days and work hours
    days = ["Monday", "Tuesday", "Wednesday"]
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Roy's busy times in minutes since 9:00 for each day
    roy_busy = {
        "Monday": [
            (10 * 60, 11 * 60 + 30),    # 10:00-11:30
            (12 * 60, 13 * 60),          # 12:00-13:00
            (14 * 60, 14 * 60 + 30),     # 14:00-14:30
            (15 * 60, 17 * 60)           # 15:00-17:00
        ],
        "Tuesday": [
            (10 * 60 + 30, 11 * 60 + 30), # 10:30-11:30
            (12 * 60, 14 * 60 + 30),      # 12:00-14:30
            (15 * 60, 15 * 60 + 30),      # 15:00-15:30
            (16 * 60, 17 * 60)            # 16:00-17:00
        ],
        "Wednesday": [
            (9 * 60 + 30, 11 * 60 + 30),  # 9:30-11:30
            (12 * 60 + 30, 14 * 60),      # 12:30-14:00
            (14 * 60 + 30, 15 * 60 + 30), # 14:30-15:30
            (16 * 60 + 30, 17 * 60)       # 16:30-17:00
        ]
    }

    # Iterate through each day in order to find the earliest possible slot
    for day in days:
        busy_intervals = roy_busy[day]
        # The available slots are the gaps between busy intervals and work hours
        available_slots = []
        previous_end = work_start

        # Sort busy intervals by start time
        sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
        
        for interval in sorted_intervals:
            start, end = interval
            if start > previous_end:
                available_slots.append((previous_end, start))
            previous_end = max(previous_end, end)
        
        # Check the slot after the last busy interval
        if previous_end < work_end:
            available_slots.append((previous_end, work_end))
        
        # Check each available slot for a meeting duration
        for slot in available_slots:
            slot_start, slot_end = slot
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                # Convert back to HH:MM format
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                # Format as 24-hour time with leading zeros
                start_time = f"{start_hh:02d}:{start_mm:02d}"
                end_time = f"{end_hh:02d}:{end_mm:02d}"
                print("SOLUTION:")
                print(f"Day: {day}")
                print(f"Start Time: {start_time}")
                print(f"End Time: {end_time}")
                return
    
    print("No solution found")

solve_scheduling()