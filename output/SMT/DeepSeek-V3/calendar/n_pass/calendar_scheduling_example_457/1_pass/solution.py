from z3 import *

def solve_scheduling():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Create a solver instance
    s = Solver()

    # Define the start time variable (in minutes from 0:00)
    start_time = Int('start_time')

    # Constraint: start time must be within work hours and leave room for the meeting
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Define each participant's busy slots in minutes
    busy_slots = {
        'Andrea': [(9*60 + 30, 10*60 + 30), (13*60 + 30, 14*60 + 30)],
        'Ruth': [(12*60 + 30, 13*60 + 0), (15*60 + 0, 15*60 + 30)],
        'Steven': [(10*60 + 0, 10*60 + 30), (11*60 + 0, 11*60 + 30), 
                   (12*60 + 0, 12*60 + 30), (13*60 + 30, 14*60 + 0), 
                   (15*60 + 0, 16*60 + 0)],
        'Grace': [],  # No meetings
        'Kyle': [(9*60 + 0, 9*60 + 30), (10*60 + 30, 12*60 + 0), 
                 (12*60 + 30, 13*60 + 0), (13*60 + 30, 15*60 + 0), 
                 (15*60 + 30, 16*60 + 0), (16*60 + 30, 17*60 + 0)],
        'Elijah': [(9*60 + 0, 11*60 + 0), (11*60 + 30, 13*60 + 0), 
                   (13*60 + 30, 14*60 + 0), (15*60 + 30, 16*60 + 0), 
                   (16*60 + 30, 17*60 + 0)],
        'Lori': [(9*60 + 0, 9*60 + 30), (10*60 + 0, 11*60 + 30), 
                 (12*60 + 0, 13*60 + 30), (14*60 + 0, 16*60 + 0), 
                 (16*60 + 30, 17*60 + 0)],
    }

    # Add constraints for each participant's busy slots
    for person in busy_slots:
        for (busy_start, busy_end) in busy_slots[person]:
            # The meeting should not overlap with any busy slot
            s.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        start_hour = start_min // 60
        start_min = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = start_hour + (end_min // 60)
        end_min = end_min % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found.")

solve_scheduling()