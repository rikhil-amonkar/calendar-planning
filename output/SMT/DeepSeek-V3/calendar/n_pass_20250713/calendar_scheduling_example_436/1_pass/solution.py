from z3 import *

def solve_meeting_schedule():
    # Participants' busy slots in minutes from 9:00 (0 minutes)
    # Each slot is (start, end) in minutes
    participants = {
        'Patrick': [(13*60 + 30 - 9*60, 14*60 - 9*60), (14*60 + 30 - 9*60, 15*60 - 9*60)],
        'Shirley': [(9*60 + 0 - 9*60, 9*60 + 30 - 9*60), (11*60 + 0 - 9*60, 11*60 + 30 - 9*60),
                    (12*60 + 0 - 9*60, 12*60 + 30 - 9*60), (14*60 + 30 - 9*60, 15*60 + 0 - 9*60),
                    (16*60 + 0 - 9*60, 17*60 + 0 - 9*60)],
        'Jeffrey': [(9*60 + 0 - 9*60, 9*60 + 30 - 9*60), (10*60 + 30 - 9*60, 11*60 + 0 - 9*60),
                    (11*60 + 30 - 9*60, 12*60 + 0 - 9*60), (13*60 + 0 - 9*60, 13*60 + 30 - 9*60),
                    (16*60 + 0 - 9*60, 17*60 + 0 - 9*60)],
        'Gloria': [(11*60 + 30 - 9*60, 12*60 + 0 - 9*60), (15*60 + 0 - 9*60, 15*60 + 30 - 9*60)],
        'Nathan': [(9*60 + 0 - 9*60, 9*60 + 30 - 9*60), (10*60 + 30 - 9*60, 12*60 + 0 - 9*60),
                   (14*60 + 0 - 9*60, 17*60 + 0 - 9*60)],
        'Angela': [(9*60 + 0 - 9*60, 9*60 + 30 - 9*60), (10*60 + 0 - 9*60, 11*60 + 0 - 9*60),
                   (12*60 + 30 - 9*60, 15*60 + 0 - 9*60), (15*60 + 30 - 9*60, 16*60 + 30 - 9*60)],
        'David': [(9*60 + 0 - 9*60, 9*60 + 30 - 9*60), (10*60 + 0 - 9*60, 10*60 + 30 - 9*60),
                  (11*60 + 0 - 9*60, 14*60 + 0 - 9*60), (14*60 + 30 - 9*60, 16*60 + 30 - 9*60)]
    }
    
    # Total available time in the day is from 9:00 (0) to 17:00 (8*60 = 480 minutes)
    max_time = 8 * 60  # 17:00 - 9:00 = 8 hours in minutes
    meeting_duration = 30
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # The meeting start time in minutes from 9:00
    start = Int('start')
    
    # Constraints: 0 <= start <= max_time - meeting_duration
    solver.add(start >= 0)
    solver.add(start <= max_time - meeting_duration)
    
    # For each participant, add constraints that the meeting does not overlap with any of their busy slots
    for person, busy_slots in participants.items():
        for (busy_start, busy_end) in busy_slots:
            # The meeting does not overlap with this busy slot if:
            # meeting ends before busy starts OR meeting starts after busy ends
            solver.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[start].as_long()
        
        # Convert start_minutes back to HH:MM format
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + meeting_duration
        hours_end = 9 + end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

solve_meeting_schedule()