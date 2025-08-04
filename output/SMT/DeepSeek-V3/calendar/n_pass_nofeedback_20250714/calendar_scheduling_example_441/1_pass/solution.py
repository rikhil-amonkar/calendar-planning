from z3 import *

def solve_scheduling():
    # Participants' busy slots in minutes from 9:00 (0 minutes)
    # Each slot is (start, end) in minutes
    participants = {
        'Joan': [(11*60 + 30 - 9*60, 12*60 - 9*60), (14*60 + 30 - 9*60, 15*60 - 9*60)],
        'Megan': [(0, 60), (14*60 - 9*60, 14*60 + 30 - 9*60), (16*60 - 9*60, 16*60 + 30 - 9*60)],
        'Austin': [],
        'Betty': [(30, 60), (11*60 + 30 - 9*60, 12*60 - 9*60), (13*60 + 30 - 9*60, 14*60 - 9*60), (16*60 - 9*60, 16*60 + 30 - 9*60)],
        'Judith': [(0, 2*60), (12*60 - 9*60, 13*60 - 9*60), (14*60 - 9*60, 15*60 - 9*60)],
        'Terry': [(30, 60), (11*60 + 30 - 9*60, 12*60 + 30 - 9*60), (13*60 - 9*60, 14*60 - 9*60), (15*60 - 9*60, 15*60 + 30 - 9*60), (16*60 - 9*60, 17*60 - 9*60)],
        'Kathryn': [(30, 60), (10*60 + 30 - 9*60, 11*60 - 9*60), (11*60 + 30 - 9*60, 13*60 - 9*60), (14*60 - 9*60, 16*60 - 9*60), (16*60 + 30 - 9*60, 17*60 - 9*60)]
    }
    
    # Total working hours: 9:00 to 17:00 (480 minutes)
    max_time = 17 * 60 - 9 * 60  # 8 hours * 60 = 480 minutes
    meeting_duration = 30
    
    # Create Z3 solver
    s = Solver()
    
    # Start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Constraints: start time must be >= 0 and <= max_time - duration
    s.add(start >= 0)
    s.add(start <= max_time - meeting_duration)
    
    # For each participant, add constraints that the meeting does not overlap with any of their busy slots
    for person, busy_slots in participants.items():
        for (busy_start, busy_end) in busy_slots:
            # The meeting does not overlap with this busy slot if:
            # meeting ends before busy starts OR meeting starts after busy ends
            s.add(Or(
                start + meeting_duration <= busy_start,
                start >= busy_end
            ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        
        # Calculate start and end times in HH:MM format
        start_hh = 9 + start_min // 60
        start_mm = start_min % 60
        end_min = start_min + meeting_duration
        end_hh = 9 + end_min // 60
        end_mm = end_min % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()