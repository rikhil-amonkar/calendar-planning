from z3 import *

def schedule_meeting():
    day = Int('day')
    start = Int('start')
    end = start + 30

    s = Optimize()

    # Constraints on day and start time
    s.add(Or(day == 0, day == 1))
    s.add(start >= 540)  # 9:00 AM
    s.add(start + 30 <= 1080)  # end by 5:00 PM

    # Constraints for Harold's availability on Monday (day 0)
    s.add(Implies(day == 0, And(start >= 600, start + 30 <= 630)))

    # Constraints for Harold's availability on Tuesday (day 1)
    s.add(Implies(day == 1, Or(
        And(start >= 570, start + 30 <= 630),  # 9:30-10:30
        And(start >= 690, start + 30 <= 750),  # 11:30-12:30
        And(start >= 810, start + 30 <= 870),  # 13:30-14:30
        And(start >= 930, start + 30 <= 960)   # 15:30-16:00
    )))

    # Optimization objectives
    s.maximize(day)  # prefer Tuesday
    s.maximize(If(day == 1, If(start >= 870, 1, 0), 0))  # prefer after 14:30 on Tuesday
    s.minimize(start)  # earliest possible

    if s.check() == sat:
        m = s.model()
        day_val = m.eval(day).as_long()
        start_val = m.eval(start).as_long()
        end_val = start_val + 30
        # Convert day to string
        day_str = "Monday" if day_val == 0 else "Tuesday"
        # Convert start_val to HH:MM
        start_h = start_val // 60
        start_m = start_val % 60
        end_h = end_val // 60
        end_m = end_val % 60
        return f"SOLUTION:\nDay: {day_str}\nStart Time: {start_h:02d}:{start_m:02d}\nEnd Time: {end_h:02d}:{end_m:02d}"
    else:
        return "No solution found"

print(schedule_meeting())