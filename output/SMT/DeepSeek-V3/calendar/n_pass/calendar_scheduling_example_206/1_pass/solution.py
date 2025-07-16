from z3 import *

def solve_scheduling():
    # Define the work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Participants' busy times in minutes since midnight
    # Each entry is (start, end)
    shirley_busy = [(10*60 + 30, 11*60), (12*60, 12*60 + 30)]
    jacob_busy = [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 11*60 + 30), 
                  (12*60 + 30, 13*60 + 30), (14*60 + 30, 15*60)]
    stephen_busy = [(11*60 + 30, 12*60), (12*60 + 30, 13*60)]
    margaret_busy = [(9*60, 9*60 + 30), (10*60 + 30, 12*60 + 30), (13*60, 13*60 + 30), 
                     (15*60, 15*60 + 30), (16*60 + 30, 17*60)]
    mason_busy = [(9*60, 10*60), (10*60 + 30, 11*60), (11*60 + 30, 12*60 + 30), 
                  (13*60, 13*60 + 30), (14*60, 14*60 + 30), (16*60 + 30, 17*60)]

    # Margaret's constraint: not before 14:30
    margaret_min_time = 14 * 60 + 30

    # Initialize Z3 solver
    solver = Solver()

    # The meeting start time in minutes since midnight (9:00 to 16:30)
    meeting_start = Int('meeting_start')
    solver.add(meeting_start >= work_start)
    solver.add(meeting_start <= work_end - meeting_duration)

    # Function to check if a time interval is free for a participant
    def is_free(busy_intervals, start, end):
        # The interval [start, end] must not overlap with any busy interval
        conditions = []
        for (busy_start, busy_end) in busy_intervals:
            conditions.append(Or(end <= busy_start, start >= busy_end))
        return And(conditions)

    # Add constraints for each participant
    solver.add(is_free(shirley_busy, meeting_start, meeting_start + meeting_duration))
    solver.add(is_free(jacob_busy, meeting_start, meeting_start + meeting_duration))
    solver.add(is_free(stephen_busy, meeting_start, meeting_start + meeting_duration))
    solver.add(is_free(mason_busy, meeting_start, meeting_start + meeting_duration))
    # Margaret's constraint: meeting must start >= 14:30
    solver.add(meeting_start >= margaret_min_time)
    # Also, Margaret's busy times must be respected
    solver.add(is_free(margaret_busy, meeting_start, meeting_start + meeting_duration))

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_min = model[meeting_start].as_long()
        start_hour = start_min // 60
        start_min_remainder = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = end_min // 60
        end_min_remainder = end_min % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_min_remainder:02d}")
        print(f"End Time: {end_hour:02d}:{end_min_remainder:02d}")
    else:
        print("No solution found")

solve_scheduling()