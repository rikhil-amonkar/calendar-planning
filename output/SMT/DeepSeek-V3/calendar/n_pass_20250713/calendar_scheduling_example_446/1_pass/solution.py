from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Work hours: 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30
    
    # Define the start time of the meeting in minutes from 0:00
    start_time = Int('start_time')
    
    # Constraint: Meeting must start and end within work hours
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)
    
    # Define each participant's busy slots in minutes
    busy_slots = {
        'Megan': [(9*60, 9*60 + 30), (10*60, 11*60), (12*60, 12*60 + 30)],
        'Christine': [(9*60, 9*60 + 30), (11*60 + 30, 12*60), (13*60, 14*60), (15*60 + 30, 16*60 + 30)],
        'Gabriel': [],
        'Sara': [(11*60 + 30, 12*60), (14*60 + 30, 15*60)],
        'Bruce': [(9*60 + 30, 10*60), (10*60 + 30, 12*60), (12*60 + 30, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 16*60 + 30)],
        'Kathryn': [(10*60, 15*60 + 30), (16*60, 16*60 + 30)],
        'Billy': [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (12*60, 14*60), (14*60 + 30, 15*60 + 30)],
    }
    
    # For each participant, add constraints that the meeting does not overlap with their busy slots
    for person, slots in busy_slots.items():
        for slot_start, slot_end in slots:
            # The meeting does not overlap with this slot if:
            # meeting ends before slot starts OR meeting starts after slot ends
            s.add(Or(
                start_time + meeting_duration <= slot_start,
                start_time >= slot_end
            ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        solution_start = m[start_time].as_long()
        
        # Convert start time from minutes to HH:MM format
        start_hh = solution_start // 60
        start_mm = solution_start % 60
        end_time = solution_start + meeting_duration
        end_hh = end_time // 60
        end_mm = end_time % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found.")

solve_scheduling()