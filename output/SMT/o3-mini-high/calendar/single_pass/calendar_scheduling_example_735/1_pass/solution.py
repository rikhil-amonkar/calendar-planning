from z3 import Optimize, Int, Or, Implies, sat

def main():
    opt = Optimize()

    # Define decision variables:
    # day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
    # start: meeting start time in minutes from 9:00, with meeting_end = start + 30.
    day = Int('day')
    start = Int('start')
    meeting_end = start + 30

    # Working hours: 9:00 to 17:00 means meeting can start from 0 to 450 minutes (since 450 + 30 = 480).
    opt.add(Or(day == 0, day == 1, day == 2))
    opt.add(start >= 0, meeting_end <= 480)

    # For each day, we add constraints that ensure the meeting does not overlap any blocked slot.
    # The blocked times are converted to minutes relative to 9:00.
    #
    # Monday:
    # Ronald's blocks: 10:30-11:00 => (90,120), 12:00-12:30 => (180,210), 15:30-16:00 => (390,420)
    # Amber's blocks: 9:00-9:30   => (0,30), 10:00-10:30 => (60,90),
    #                11:30-12:00 => (150,180), 12:30-14:00 => (210,300),
    #                14:30-15:00 => (330,360), 15:30-17:00 => (390,480)
    monday_blocks = [
        # Ronald's blocks
        (90, 120),
        (180, 210),
        (390, 420),
        # Amber's blocks
        (0, 30),
        (60, 90),
        (150, 180),
        (210, 300),
        (330, 360),
        (390, 480)
    ]
    for (b_start, b_end) in monday_blocks:
        # For Monday (day == 0), the meeting must either end by the block's start or start after the block's end.
        opt.add(Implies(day == 0, Or(meeting_end <= b_start, start >= b_end)))

    # Tuesday:
    # Ronald's blocks: 9:00-9:30   => (0,30), 12:00-12:30 => (180,210), 15:30-16:30 => (390,450)
    # Amber's blocks: 9:00-9:30   => (0,30), 10:00-11:30 => (60,150),
    #                12:00-12:30 => (180,210), 13:30-15:30 => (270,390),
    #                16:30-17:00 => (450,480)
    tuesday_blocks = [
        # Ronald's blocks
        (0, 30),
        (180, 210),
        (390, 450),
        # Amber's blocks
        (0, 30),
        (60, 150),
        (180, 210),
        (270, 390),
        (450, 480)
    ]
    for (b_start, b_end) in tuesday_blocks:
        opt.add(Implies(day == 1, Or(meeting_end <= b_start, start >= b_end)))

    # Wednesday:
    # Ronald's blocks: 9:30-10:30 => (30,90), 11:00-12:00 => (120,180), 12:30-13:00 => (210,240),
    #                   13:30-14:00 => (270,300), 16:30-17:00 => (450,480)
    # Amber's blocks: 9:00-9:30   => (0,30), 10:00-10:30 => (60,90),
    #                11:00-13:30 => (120,270), 15:00-15:30 => (360,390)
    wednesday_blocks = [
        # Ronald's blocks
        (30, 90),
        (120, 180),
        (210, 240),
        (270, 300),
        (450, 480),
        # Amber's blocks
        (0, 30),
        (60, 90),
        (120, 270),
        (360, 390)
    ]
    for (b_start, b_end) in wednesday_blocks:
        opt.add(Implies(day == 2, Or(meeting_end <= b_start, start >= b_end)))

    # The group would like to meet at their earliest availability.
    # We set an objective to minimize the day (Monday preferred over Tuesday over Wednesday)
    # and then minimize the meeting start time within that day.
    opt.minimize(day)
    opt.minimize(start)

    # Check the constraints and extract the solution.
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        end_val = start_val + 30

        # Map the integer day back to the day name.
        day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
        meeting_day = day_names.get(d_val, "Unknown")

        # Convert meeting start and end (in minutes offset from 9:00) into HH:MM format.
        def format_time(mins_offset):
            total_minutes = 9 * 60 + mins_offset
            hour = total_minutes // 60
            minute = total_minutes % 60
            return f"{hour:02d}:{minute:02d}"

        start_time_str = format_time(start_val)
        end_time_str = format_time(end_val)

        # Print the solution in the required format.
        print("SOLUTION:")
        print(f"Day: {meeting_day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()