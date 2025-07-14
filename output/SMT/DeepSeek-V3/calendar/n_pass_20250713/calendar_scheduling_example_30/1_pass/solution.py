from z3 import *

def find_meeting_time():
    # Define the work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define the participants' busy slots in minutes since midnight
    jeffrey_busy = [(9*60 + 30, 10*60), (10*60 + 30, 11*60)]
    virginia_busy = [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (14*60 + 30, 15*60), (16*60, 16*60 + 30)]
    melissa_busy = [(9*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 15*60), (16*60, 17*60)]
    
    # Melissa's preference: not after 14:00, so meeting must end by 14:00
    preference_end = 14 * 60

    # Create a Z3 solver instance
    solver = Solver()

    # Define the meeting start time variable (in minutes)
    start_time = Int('start_time')

    # Add constraints for the meeting to be within work hours
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)

    # Add constraint for Melissa's preference: meeting must end by 14:00
    solver.add(start_time + meeting_duration <= preference_end)

    # Add constraints to avoid busy times for each participant
    def add_busy_constraints(busy_slots):
        for start, end in busy_slots:
            # The meeting should not overlap with any busy slot
            solver.add(Or(
                start_time + meeting_duration <= start,
                start_time >= end
            ))

    add_busy_constraints(jeffrey_busy)
    add_busy_constraints(virginia_busy)
    add_busy_constraints(melissa_busy)

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start = model[start_time].as_long()
        # Convert minutes back to HH:MM format
        start_hh = start // 60
        start_mm = start % 60
        end = start + meeting_duration
        end_hh = end // 60
        end_mm = end % 60
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

find_meeting_time()