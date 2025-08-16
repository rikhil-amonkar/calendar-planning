from z3 import *

def main():
    duration = 30  # meeting duration in minutes
    # Define meeting start time as the number of minutes since midnight.
    # Workday is from 9:00 (540 minutes) to 17:00 (1020 minutes). 
    start = Int('start')
    
    solver = Solver()
    # Ensure the meeting starts and finishes within work hours.
    solver.add(start >= 540, start + duration <= 1020)
    
    # Define the busy intervals (in minutes) for each participant.
    # Each tuple represents (busy_start, busy_end).
    busy_intervals = [
        # Bradley's busy times
        (570, 600),   # 9:30 to 10:00
        (750, 780),   # 12:30 to 13:00
        (810, 840),   # 13:30 to 14:00
        (930, 960),   # 15:30 to 16:00
        # Teresa's busy times
        (630, 660),   # 10:30 to 11:00
        (720, 750),   # 12:00 to 12:30
        (780, 810),   # 13:00 to 13:30
        (870, 900),   # 14:30 to 15:00
        # Elizabeth's busy times
        (540, 570),   # 9:00 to 9:30
        (630, 690),   # 10:30 to 11:30
        (780, 810),   # 13:00 to 13:30
        (870, 900),   # 14:30 to 15:00
        (930, 1020),  # 15:30 to 17:00
        # Christian's busy times
        (540, 570),   # 9:00 to 9:30
        (630, 1020)   # 10:30 to 17:00
    ]
    
    # For each busy interval, the meeting must not overlap.
    # That is, for each interval [b_start, b_end), either the meeting finishes
    # before b_start, or it starts after b_end.
    for (b_start, b_end) in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))
    
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration

        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02}:{mins:02}"

        # Output the solution in the required format.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time:", format_time(meeting_start))
        print("End Time:", format_time(meeting_end))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()