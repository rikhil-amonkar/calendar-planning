from z3 import *

def solve_scheduling():
    # Define the days and work hours
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Define the participants' schedules in minutes since midnight
    # Arthur's schedule: day -> list of (start, end) in minutes
    arthur_schedule = {
        'Monday': [(11*60, 11*60 + 30), (13*60 + 30, 14*60), (15*60, 15*60 + 30)],
        'Tuesday': [(13*60, 13*60 + 30), (16*60, 16*60 + 30)],
        'Wednesday': [(10*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (14*60, 14*60 + 30), (16*60, 16*60 + 30)]
    }
    
    # Michael's schedule
    michael_schedule = {
        'Monday': [(9*60, 12*60), (12*60 + 30, 13*60), (14*60, 14*60 + 30), (15*60, 17*60)],
        'Tuesday': [(9*60 + 30, 11*60 + 30), (12*60, 13*60 + 30), (14*60, 15*60 + 30)],
        'Wednesday': [(10*60, 12*60 + 30), (13*60, 13*60 + 30)]
    }
    
    # Arthur cannot meet on Tuesday
    available_days = ['Monday', 'Wednesday']
    
    meeting_duration = 30  # minutes
    
    # Iterate through each day in order to find the earliest possible slot
    for day in available_days:
        # Generate all possible 30-minute slots in the work hours
        for start in range(work_start, work_end - meeting_duration + 1, 5):  # step by 5 minutes for efficiency
            end = start + meeting_duration
            if end > work_end:
                continue
            
            # Check if Arthur is free during this slot
            arthur_free = True
            for (busy_start, busy_end) in arthur_schedule[day]:
                if not (end <= busy_start or start >= busy_end):
                    arthur_free = False
                    break
            if not arthur_free:
                continue
            
            # Check if Michael is free during this slot
            michael_free = True
            for (busy_start, busy_end) in michael_schedule[day]:
                if not (end <= busy_start or start >= busy_end):
                    michael_free = False
                    break
            if not michael_free:
                continue
            
            # If both are free, this is the earliest possible slot
            # Convert start and end back to HH:MM format
            start_hh = start // 60
            start_mm = start % 60
            end_hh = end // 60
            end_mm = end % 60
            
            print(f"SOLUTION:")
            print(f"Day: {day}")
            print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
            print(f"End Time: {end_hh:02d}:{end_mm:02d}")
            return
    
    print("No solution found")

solve_scheduling()