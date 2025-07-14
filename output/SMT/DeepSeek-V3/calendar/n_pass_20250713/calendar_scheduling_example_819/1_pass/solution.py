from z3 import *

def solve_meeting_scheduling():
    # Create the solver
    s = Solver()

    # Define the variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 = 9:00, 30 = 9:30, etc.)

    # Meeting duration is fixed to 30 minutes
    duration = 30
    end_time = start_time + duration

    # Constraints for day: must be 0 (Monday), 1 (Tuesday), 2 (Wednesday), or 3 (Thursday)
    s.add(day >= 0, day <= 3)

    # Constraints for start_time: must be between 9:00 (0 minutes) and 16:30 (450 minutes) to fit the 30-minute meeting
    s.add(start_time >= 0, start_time <= 450)  # 17:00 - 0:30 = 16:30 (450 minutes)

    # Julie's constraints: no meetings, but prefers to avoid Thursday before 11:30
    # So if day is Thursday (3), start_time must be >= 150 minutes (11:30 - 9:00 = 2.5 hours = 150 minutes)
    s.add(If(day == 3, start_time >= 150, True))

    # Ruth's constraints:
    # Monday (0): busy all day (9:00-17:00) -> no possible time
    # Tuesday (1): busy all day (9:00-17:00) -> no possible time
    # Wednesday (2): busy all day (9:00-17:00) -> no possible time
    # Thursday (3): busy 9:00-11:00, 11:30-14:30, 15:00-17:00
    # So on Thursday, possible slots are:
    # - 11:00-11:30 (but this is only 30 minutes, which fits the meeting)
    # - 14:30-15:00 (also 30 minutes)
    # So the meeting must be in one of these two slots on Thursday.

    # Ruth's constraints encoded:
    s.add(If(day == 0, False,  # Monday: no time available
          If(day == 1, False,  # Tuesday: no time available
          If(day == 2, False,  # Wednesday: no time available
          If(day == 3, Or(
              And(start_time >= 120, end_time <= 150),  # 11:00-11:30 (120 to 150 minutes)
              And(start_time >= 270, end_time <= 300)   # 14:30-15:00 (270 to 300 minutes)
          ), False)))))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_time_val = model[start_time].as_long()

        # Map day_val to day string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[day_val]

        # Calculate start and end times in HH:MM format
        start_hour = 9 + start_time_val // 60
        start_minute = start_time_val % 60
        end_time_val = start_time_val + duration
        end_hour = 9 + end_time_val // 60
        end_minute = end_time_val % 60

        # Format as HH:MM
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

# Run the solver
solve_meeting_scheduling()