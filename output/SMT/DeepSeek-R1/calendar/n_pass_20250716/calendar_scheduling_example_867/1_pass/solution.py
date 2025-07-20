from z3 import *

def main():
    # Define the variables
    day = Int('day')
    start = Int('start')   # in minutes from 9:00

    # Define the busy intervals for Betty and Scott for Wednesday (2) and Thursday (3)
    betty_busy = {
        2: [(30, 90), (240, 270), (300, 330)],   # Wednesday
        3: [(360, 390), (450, 480)]              # Thursday
    }
    scott_busy = {
        2: [(30, 210), (240, 270), (300, 330), (360, 390), (420, 450)],
        3: [(360, 420), (450, 480)]
    }

    s = Solver()

    # Constraint: day is either 2 (Wednesday) or 3 (Thursday)
    s.add(Or(day == 2, day == 3))

    # The meeting must be scheduled within 9:00 to 17:00 -> 0 to 480 minutes from 9:00, and duration 30 -> so start in [0, 450]
    s.add(start >= 0, start <= 450)

    # Betty's constraint: on Thursday, the meeting cannot start before 15:00 (which is 360 minutes from 9:00)
    s.add(If(day == 3, start >= 360, True))

    # For Betty: condition on the busy intervals for the chosen day
    wed_betty = []
    for (bs, be) in betty_busy[2]:
        wed_betty.append(Or(start + 30 <= bs, start >= be))
    thu_betty = []
    for (bs, be) in betty_busy[3]:
        thu_betty.append(Or(start + 30 <= bs, start >= be))
    s.add(If(day == 2, And(wed_betty), And(thu_betty)))

    # For Scott
    wed_scott = []
    for (bs, be) in scott_busy[2]:
        wed_scott.append(Or(start + 30 <= bs, start >= be))
    thu_scott = []
    for (bs, be) in scott_busy[3]:
        thu_scott.append(Or(start + 30 <= bs, start >= be))
    s.add(If(day == 2, And(wed_scott), And(thu_scott)))

    # Prefer Thursday (day 3) to avoid Wednesday (Scott's preference)
    s.push()
    s.add(day == 3)
    if s.check() == sat:
        m = s.model()
        s.pop()
        day_val = m[day].as_long()
        start_val = m[start].as_long()
    else:
        s.pop()
        s.push()
        s.add(day == 2)
        if s.check() == sat:
            m = s.model()
            s.pop()
            day_val = m[day].as_long()
            start_val = m[start].as_long()
        else:
            print("No solution found")
            exit(1)

    # Map day_val to day string
    day_str = {2: "Wednesday", 3: "Thursday"}[day_val]

    # Convert start_val to time string
    total_minutes = start_val
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_hour = 9 + hours
    start_minute = minutes
    start_time = f"{start_hour}:{minutes:02d}"

    # End time is 30 minutes later
    end_val = start_val + 30
    hours_end = end_val // 60
    minutes_end = end_val % 60
    end_hour = 9 + hours_end
    end_time = f"{end_hour}:{minutes_end:02d}"

    # Print the solution
    print(f"Day: {day_str}")
    print(f"Start time: {start_time}")
    print(f"End time: {end_time}")

if __name__ == "__main__":
    main()