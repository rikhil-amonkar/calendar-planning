from z3 import *

def solve_meeting_scheduling():
    # Create a solver instance
    s = Solver()

    # Define the possible days: Monday (0), Tuesday (1), Wednesday (2)
    day = Int('day')
    s.add(day >= 0, day <= 2)  # 0: Monday, 1: Tuesday, 2: Wednesday

    # Cheryl cannot meet on Wednesday, so day must be 0 or 1
    s.add(Or(day == 0, day == 1))

    # Define start time in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 990)  # 990 = 16:30, as meeting duration is 30 minutes

    # Meeting duration is 30 minutes
    end_time = start_time + 30
    s.add(end_time <= 1020)  # Ensure end time is not beyond 17:00

    # Cheryl's busy slots
    # Monday: 9:00-9:30 (540-570), 11:30-13:00 (690-780), 15:30-16:00 (930-960)
    # Tuesday: 15:00-15:30 (900-930)
    def cheryl_busy(d, st, et):
        return Or(
            And(d == 0, Or(
                And(st < 570, et > 540),   # overlaps with 9:00-9:30
                And(st < 780, et > 690),   # overlaps with 11:30-13:00
                And(st < 960, et > 930)    # overlaps with 15:30-16:00
            )),
            And(d == 1, And(st < 930, et > 900))  # overlaps with 15:00-15:30 on Tuesday
        )

    # Kyle's busy slots
    # Monday: 9:00-17:00 (540-1020) → entire day, so no available time on Monday
    # Tuesday: 9:30-17:00 (570-1020)
    # Wednesday: 9:00-9:30 (540-570), 10:00-13:00 (600-780), 13:30-14:00 (810-840), 14:30-17:00 (870-1020)
    def kyle_busy(d, st, et):
        return Or(
            And(d == 0, Or(And(st < 1020, et > 540))),  # entire Monday is busy
            And(d == 1, Or(And(st < 1020, et > 570))),  # Tuesday after 9:30
            And(d == 2, Or(
                And(st < 570, et > 540),   # 9:00-9:30
                And(st < 780, et > 600),   # 10:00-13:00
                And(st < 840, et > 810),   # 13:30-14:00
                And(st < 1020, et > 870)    # 14:30-17:00
            ))
        )

    # The meeting time should not overlap with any busy slots for Cheryl or Kyle
    s.add(Not(cheryl_busy(day, start_time, end_time)))
    s.add(Not(kyle_busy(day, start_time, end_time)))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = start_val + 30

        # Convert day number to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[day_val]

        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(end_val)

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_scheduling()