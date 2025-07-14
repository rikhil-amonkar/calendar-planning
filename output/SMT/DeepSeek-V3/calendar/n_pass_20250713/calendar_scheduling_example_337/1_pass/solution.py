from z3 import *

def solve_meeting_scheduling():
    # Participants' schedules on Monday
    schedules = {
        'John': [(11 * 60 + 30, 12 * 60), (14 * 60, 14 * 60 + 30)],
        'Megan': [(12 * 60, 12 * 60 + 30), (14 * 60, 15 * 60), (15 * 60 + 30, 16 * 60)],
        'Brandon': [],
        'Kimberly': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
        'Sean': [(10 * 60, 11 * 60), (11 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30)],
        'Lori': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (13 * 60, 14 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    }
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Work hours: 9:00 to 17:00 (9*60 to 17*60 in minutes)
    start_work = 9 * 60
    end_work = 17 * 60
    
    # Create Z3 solver
    s = Solver()
    
    # Variable for the meeting start time (in minutes from 00:00, but constrained within work hours)
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= start_work)
    s.add(meeting_start + duration <= end_work)
    
    # For each participant, add constraints that the meeting does not overlap with their busy times
    for person, busy_slots in schedules.items():
        for (busy_start, busy_end) in busy_slots:
            # The meeting should not overlap with this busy slot
            # So either meeting ends before busy starts or meeting starts after busy ends
            s.add(Or(
                meeting_start + duration <= busy_start,
                meeting_start >= busy_end
            ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m[meeting_start].as_long()
        
        # Convert start_minutes to HH:MM
        hh = start_minutes // 60
        mm = start_minutes % 60
        start_time = f"{hh:02d}:{mm:02d}"
        
        end_minutes = start_minutes + duration
        hh_end = end_minutes // 60
        mm_end = end_minutes % 60
        end_time = f"{hh_end:02d}:{mm_end:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

solve_meeting_scheduling()