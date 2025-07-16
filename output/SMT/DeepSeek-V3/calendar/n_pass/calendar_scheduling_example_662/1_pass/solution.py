from z3 import *

def solve_meeting_scheduling():
    # Define the possible days
    days = ['Monday', 'Tuesday']
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Meeting duration is 1 hour (60 minutes)
    meeting_duration = 60
    
    # Define the blocked times for Gary and David for each day in minutes since midnight
    blocked_times = {
        'Gary': {
            'Monday': [(9*60 + 30, 10*60), (11*60, 13*60), (14*60, 14*60 + 30), (16*60 + 30, 17*60)],
            'Tuesday': [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (14*60 + 30, 16*60)]
        },
        'David': {
            'Monday': [(9*60, 9*60 + 30), (10*60, 13*60), (14*60 + 30, 16*60 + 30)],
            'Tuesday': [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 12*60 + 30), 
                        (13*60, 14*60 + 30), (15*60, 16*60), (16*60 + 30, 17*60)]
        }
    }
    
    # Iterate through each day and each possible start time to find a valid slot
    for day in days:
        for start in range(work_start, work_end - meeting_duration + 1):
            end = start + meeting_duration
            valid = True
            
            # Check Gary's schedule
            for (block_start, block_end) in blocked_times['Gary'][day]:
                if not (end <= block_start or start >= block_end):
                    valid = False
                    break
            if not valid:
                continue
            
            # Check David's schedule
            for (block_start, block_end) in blocked_times['David'][day]:
                if not (end <= block_start or start >= block_end):
                    valid = False
                    break
            if valid:
                # Convert start and end times back to HH:MM format
                start_hh = start // 60
                start_mm = start % 60
                end_hh = end // 60
                end_mm = end % 60
                
                print(f"SOLUTION:")
                print(f"Day: {day}")
                print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
                print(f"End Time: {end_hh:02d}:{end_mm:02d}")
                return
    
    print("No valid meeting time found.")

solve_meeting_scheduling()