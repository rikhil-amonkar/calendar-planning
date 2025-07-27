from z3 import *

def find_meeting_time():
    # Participants and their busy slots on Monday (in 24-hour format)
    busy_slots = {
        'Judy': [(13, 0, 13, 30), (16, 0, 16, 30)],
        'Olivia': [(10, 0, 10, 30), (12, 0, 13, 0), (14, 0, 14, 30)],
        'Eric': [],  # Free all day
        'Jacqueline': [(10, 0, 10, 30), (15, 0, 15, 30)],
        'Laura': [(9, 0, 10, 0), (10, 30, 12, 0), (13, 0, 13, 30), (14, 30, 15, 0), (15, 30, 17, 0)],
        'Tyler': [(9, 0, 10, 0), (11, 0, 11, 30), (12, 30, 13, 0), (14, 0, 14, 30), (15, 30, 17, 0)],
        'Lisa': [(9, 30, 10, 30), (11, 0, 11, 30), (12, 0, 12, 30), (13, 0, 13, 30), (14, 0, 14, 30), (16, 0, 17, 0)]
    }
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Work hours are 9:00 to 17:00 (9:00 AM to 5:00 PM)
    work_start = (9, 0)   # 9:00 AM
    work_end = (17, 0)     # 5:00 PM
    
    # Convert all times to minutes since 00:00 for easier calculation
    def time_to_minutes(hour, minute):
        return hour * 60 + minute
    
    work_start_min = time_to_minutes(*work_start)
    work_end_min = time_to_minutes(*work_end)
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # The meeting start time in minutes since 00:00
    meeting_start = Int('meeting_start')
    
    # Constraints:
    # 1. Meeting must start within work hours and end before work ends
    solver.add(meeting_start >= work_start_min)
    solver.add(meeting_start + duration <= work_end_min)
    
    # 2. For each participant, the meeting must not overlap with any of their busy slots
    for person, slots in busy_slots.items():
        for (start_h, start_m, end_h, end_m) in slots:
            start = time_to_minutes(start_h, start_m)
            end = time_to_minutes(end_h, end_m)
            # The meeting should not overlap with this busy slot
            solver.add(Or(
                meeting_start + duration <= start,
                meeting_start >= end
            ))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_min = model[meeting_start].as_long()
        # Convert back to HH:MM format
        start_h = start_min // 60
        start_m = start_min % 60
        end_min = start_min + duration
        end_h = end_min // 60
        end_m = end_min % 60
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_h:02d}:{start_m:02d}")
        print(f"End Time: {end_h:02d}:{end_m:02d}")
    else:
        print("No solution found.")

find_meeting_time()