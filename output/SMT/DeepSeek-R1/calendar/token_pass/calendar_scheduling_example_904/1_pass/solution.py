from z3 import Int, And, Or, If, Solver, sat

def main():
    # Define the variables
    day = Int('day')
    start_time = Int('start_time')  # in minutes from 9:00

    s = Solver()

    # Define days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_day_start = 0   # 9:00 in minutes from 9:00
    work_day_end = 480   # 17:00 in minutes from 9:00
    meeting_duration = 30

    # Daniel's busy blocks in minutes from 9:00 for each day
    daniel_busy = {
        0: [(30, 90), (180, 210), (240, 300), (330, 360), (390, 420)],   # Monday
        1: [(120, 180), (240, 270), (390, 420), (450, 480)],             # Tuesday
        2: [(0, 60), (300, 330)],                                        # Wednesday
        3: [(90, 120), (180, 240), (330, 360), (390, 420)],              # Thursday
        4: [(0, 30), (150, 180), (240, 270), (450, 480)]                 # Friday
    }

    # Bradley's busy blocks in minutes from 9:00 for each day
    bradley_busy = {
        0: [(30, 120), (150, 180), (210, 240), (300, 360)],              # Monday
        1: [(90, 120), (180, 240), (270, 300), (390, 450)],              # Tuesday
        2: [(0, 60), (120, 240), (270, 300), (330, 480)],                # Wednesday
        3: [(0, 210), (270, 300), (330, 360), (390, 450)],               # Thursday
        4: [(0, 30), (60, 210), (240, 270), (300, 330), (390, 450)]      # Friday
    }

    # Constraints for day and time within work hours
    s.add(day >= 0, day <= 4)
    s.add(start_time >= work_day_start)
    s.add(start_time + meeting_duration <= work_day_end)

    # Participant preferences
    # Daniel: not Wednesday (2) and not Thursday (3)
    s.add(day != 2, day != 3)
    # Bradley: not Monday (0), not Friday (4), and on Tuesday (1) only after 12:00 (180 minutes)
    s.add(day != 0, day != 4)
    s.add(If(day == 1, start_time >= 180, True))

    # For each day, add constraints that the meeting does not overlap with busy blocks
    for d in range(5):
        # Daniel's busy blocks for day d
        for block in daniel_busy[d]:
            s.add(If(day == d, Or(start_time + meeting_duration <= block[0], start_time >= block[1]), True))
        # Bradley's busy blocks for day d
        for block in bradley_busy[d]:
            s.add(If(day == d, Or(start_time + meeting_duration <= block[0], start_time >= block[1]), True))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start_time].as_long()
        
        # Calculate start time in HH:MM format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_val = start_val + meeting_duration
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        
        # Format the time strings
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"{days[d_val]}")
        print(f"{start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()