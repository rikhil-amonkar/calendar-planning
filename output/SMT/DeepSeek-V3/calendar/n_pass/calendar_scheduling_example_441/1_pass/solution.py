from z3 import *

def find_meeting_time():
    # Participants and their busy slots in minutes since 9:00 (540 minutes)
    # Each busy slot is (start, end) in minutes from 9:00
    participants = {
        "Joan": [(11*60 + 30 - 540, 12*60 - 540), (14*60 + 30 - 540, 15*60 - 540)],
        "Megan": [(9*60 - 540, 10*60 - 540), (14*60 - 540, 14*60 + 30 - 540), (16*60 - 540, 16*60 + 30 - 540)],
        "Austin": [],
        "Betty": [(9*60 + 30 - 540, 10*60 - 540), (11*60 + 30 - 540, 12*60 - 540), (13*60 + 30 - 540, 14*60 - 540), (16*60 - 540, 16*60 + 30 - 540)],
        "Judith": [(9*60 - 540, 11*60 - 540), (12*60 - 540, 13*60 - 540), (14*60 - 540, 15*60 - 540)],
        "Terry": [(9*60 + 30 - 540, 10*60 - 540), (11*60 + 30 - 540, 12*60 + 30 - 540), (13*60 - 540, 14*60 - 540), (15*60 - 540, 15*60 + 30 - 540), (16*60 - 540, 17*60 - 540)],
        "Kathryn": [(9*60 + 30 - 540, 10*60 - 540), (10*60 + 30 - 540, 11*60 - 540), (11*60 + 30 - 540, 13*60 - 540), (14*60 - 540, 16*60 - 540), (16*60 + 30 - 540, 17*60 - 540)],
    }
    
    # Total work hours in minutes (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 8 * 60
    
    # Create Z3 solver
    s = Solver()
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Variable for the start time of the meeting (in minutes from 9:00)
    start = Int('start')
    
    # Constraints: start time must be within work hours and allow for the meeting duration
    s.add(start >= 0)
    s.add(start + meeting_duration <= total_minutes)
    
    # For each participant, the meeting must not overlap with any of their busy slots
    for person, busy_slots in participants.items():
        for (busy_start, busy_end) in busy_slots:
            # The meeting does not overlap with this busy slot if:
            # meeting ends before busy starts OR meeting starts after busy ends
            s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_time_min = m[start].as_long()
        
        # Convert start time from minutes to HH:MM
        start_hh = 9 + start_time_min // 60
        start_mm = start_time_min % 60
        start_time = f"{start_hh:02d}:{start_mm:02d}"
        
        # Calculate end time
        end_time_min = start_time_min + meeting_duration
        end_hh = 9 + end_time_min // 60
        end_mm = end_time_min % 60
        end_time = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found.")

find_meeting_time()