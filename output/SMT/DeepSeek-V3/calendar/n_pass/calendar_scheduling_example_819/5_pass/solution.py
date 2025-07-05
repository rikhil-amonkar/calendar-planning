from z3 import *

def solve_meeting_scheduling():
    s = Solver()

    # Define variables
    day = Int('day')  # 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    start_time = Int('start_time')  # Minutes from 9:00 (0=9:00, 30=9:30, etc.)
    duration = 30
    end_time = start_time + duration

    # Day must be Monday-Thursday (0-3)
    s.add(day >= 0, day <= 3)

    # Meeting must fit within work hours (9:00-17:00)
    s.add(start_time >= 0, end_time <= 480)  # 17:00 = 8 hours = 480 minutes

    # Julie's preference: Avoid Thursday before 11:30 (150 minutes)
    s.add(If(day == 3, start_time >= 150, True))

    # Ruth's availability constraints
    # Monday: completely busy (9:00-17:00)
    s.add(If(day == 0, False, True))
    
    # Tuesday: completely busy (9:00-17:00)
    s.add(If(day == 1, False, True))
    
    # Wednesday: completely busy (9:00-17:00)
    s.add(If(day == 2, False, True))
    
    # Thursday: busy periods are 9:00-11:00, 11:30-14:30, 15:00-17:00
    # So available slots are:
    # 11:00-11:30 (120-150 minutes) - but Julie prefers to avoid before 11:30
    # 14:30-15:00 (270-300 minutes) - only valid option
    s.add(If(day == 3, 
          And(start_time >= 270, end_time <= 300),  # Only allow 14:30-15:00
          True)

    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_time_val = model[start_time].as_long()

        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[day_val]

        start_h = 9 + start_time_val // 60
        start_m = start_time_val % 60
        end_time_val = start_time_val + duration
        end_h = 9 + end_time_val // 60
        end_m = end_time_val % 60

        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_h:02d}:{start_m:02d}")
        print(f"End Time: {end_h:02d}:{end_m:02d}")
    else:
        print("No valid meeting time found")

solve_meeting_scheduling()