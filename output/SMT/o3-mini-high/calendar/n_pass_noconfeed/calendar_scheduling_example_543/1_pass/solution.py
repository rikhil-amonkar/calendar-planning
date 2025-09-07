from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    meeting_duration = 60
    work_start = 9 * 60    # 9:00 AM in minutes (540)
    work_end = 17 * 60     # 17:00 in minutes (1020)

    # Create a Z3 solver instance
    solver = Solver()
    start = Int('start')  # Meeting start time in minutes from midnight

    # Constraint: Meeting must be within work hours.
    solver.add(start >= work_start, start + meeting_duration <= work_end)
    
    # James's busy intervals on Monday:
    # Busy from 11:30 (690) to 12:00 (720)
    solver.add(Or(start + meeting_duration <= 690, start >= 720))
    # Busy from 14:30 (870) to 15:00 (900)
    solver.add(Or(start + meeting_duration <= 870, start >= 900))
    
    # John's busy intervals on Monday:
    # Busy from 9:30 (570) to 11:00 (660)
    solver.add(Or(start + meeting_duration <= 570, start >= 660))
    # Busy from 11:30 (690) to 12:00 (720)
    solver.add(Or(start + meeting_duration <= 690, start >= 720))
    # Busy from 12:30 (750) to 13:30 (810)
    solver.add(Or(start + meeting_duration <= 750, start >= 810))
    # Busy from 14:30 (870) to 16:30 (990)
    solver.add(Or(start + meeting_duration <= 870, start >= 990))
    
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + meeting_duration
        start_time = minutes_to_time(meeting_start)
        end_time = minutes_to_time(meeting_end)
        day = "Monday"
        # Output in the format: Day {HH:MM:HH:MM}
        print(f"{day} {{{start_time}:{end_time}}}")
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()