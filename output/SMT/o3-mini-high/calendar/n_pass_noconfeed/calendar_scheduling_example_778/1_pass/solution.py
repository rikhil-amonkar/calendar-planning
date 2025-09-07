from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return "{:02d}:{:02d}".format(hours, mins)

def main():
    solver = Solver()
    
    # Variables:
    # day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
    day = Int('day')
    # start time in minutes from midnight. (Working hours: 9:00 = 540 minutes, 17:00 = 1020 minutes)
    start = Int('start')
    
    # Domain for day and working hours constraint for the meeting.
    solver.add(Or(day == 0, day == 1, day == 2))
    # Susan would rather not meet on Tuesday.
    solver.add(day != 1)
    # Meeting duration is 30 minutes. To finish by 17:00, start must be at most 990.
    solver.add(start >= 540, start + 30 <= 1020)
    
    # Additional constraint: On Monday, Sandra cannot meet after 16:00 (i.e. meeting must end by 16:00).
    solver.add(Implies(day == 0, start + 30 <= 960))
    
    # Helper: For any busy interval [a, b], the meeting [start, start+30] must either end by a or start after b.
    # Non-overlap condition: (start + 30) <= busy_start or start >= busy_end.

    # Susan's busy intervals:
    # Monday: 12:30-13:00 (750,780), 13:30-14:00 (810,840)
    solver.add(Implies(day == 0, Or(start + 30 <= 750, start >= 780)))
    solver.add(Implies(day == 0, Or(start + 30 <= 810, start >= 840)))
    # Tuesday: 11:30-12:00 (690,720) -- (won't be chosen due to preference, but added for completeness)
    solver.add(Implies(day == 1, Or(start + 30 <= 690, start >= 720)))
    # Wednesday: 9:30-10:30 (570,630), 14:00-14:30 (840,870), 15:30-16:30 (930,990)
    solver.add(Implies(day == 2, Or(start + 30 <= 570, start >= 630)))
    solver.add(Implies(day == 2, Or(start + 30 <= 840, start >= 870)))
    solver.add(Implies(day == 2, Or(start + 30 <= 930, start >= 990)))
    
    # Sandra's busy intervals:
    # Monday: 9:00-13:00 (540,780), 14:00-15:00 (840,900), 16:00-16:30 (960,990)
    solver.add(Implies(day == 0, Or(start + 30 <= 540, start >= 780)))
    solver.add(Implies(day == 0, Or(start + 30 <= 840, start >= 900)))
    solver.add(Implies(day == 0, Or(start + 30 <= 960, start >= 990)))
    # Tuesday: 9:00-9:30 (540,570), 10:30-12:00 (630,720), 12:30-13:30 (750,810),
    #          14:00-14:30 (840,870), 16:00-17:00 (960,1020)
    solver.add(Implies(day == 1, Or(start + 30 <= 540, start >= 570)))
    solver.add(Implies(day == 1, Or(start + 30 <= 630, start >= 720)))
    solver.add(Implies(day == 1, Or(start + 30 <= 750, start >= 810)))
    solver.add(Implies(day == 1, Or(start + 30 <= 840, start >= 870)))
    solver.add(Implies(day == 1, Or(start + 30 <= 960, start >= 1020)))
    # Wednesday: 9:00-11:30 (540,690), 12:00-12:30 (720,750), 13:00-17:00 (780,1020)
    solver.add(Implies(day == 2, Or(start + 30 <= 540, start >= 690)))
    solver.add(Implies(day == 2, Or(start + 30 <= 720, start >= 750)))
    solver.add(Implies(day == 2, Or(start + 30 <= 780, start >= 1020)))
    
    if solver.check() == sat:
        model = solver.model()
        meeting_day_val = model[day].as_long()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + 30
        
        day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
        meeting_day = day_map[meeting_day_val]
        start_str = format_time(meeting_start)
        end_str = format_time(meeting_end)
        # Output format: Day HH:MM:HH:MM (start and end times separated by a colon)
        print(f"{meeting_day} {start_str}:{end_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()