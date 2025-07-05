from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Create a solver instance
    s = Solver()

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= work_start)
    s.add(meeting_start + meeting_duration <= work_end)

    # Each person's busy intervals in minutes since 9:00
    patrick_busy = [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (13*60 + 30, 14*60), (16*60, 16*60 + 30)]
    kayla_busy = [(12*60 + 30, 13*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
    carl_busy = [(10*60 + 30, 11*60), (12*60, 12*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 17*60)]
    christian_busy = [(9*60, 12*60 + 30), (13*60, 14*60), (14*60 + 30, 17*60)]

    # Function to check if the meeting overlaps with any busy interval
    def no_overlap(start, duration, busy_intervals):
        constraints = []
        for (busy_start, busy_end) in busy_intervals:
            constraints.append(Or(start + duration <= busy_start, start >= busy_end))
        return And(*constraints)

    # Add constraints for each person
    s.add(no_overlap(meeting_start, meeting_duration, patrick_busy))
    s.add(no_overlap(meeting_start, meeting_duration, kayla_busy))
    s.add(no_overlap(meeting_start, meeting_duration, carl_busy))
    s.add(no_overlap(meeting_start, meeting_duration, christian_busy))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[meeting_start].as_long()
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = end_min // 60
        end_minute = end_min % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

find_meeting_time()