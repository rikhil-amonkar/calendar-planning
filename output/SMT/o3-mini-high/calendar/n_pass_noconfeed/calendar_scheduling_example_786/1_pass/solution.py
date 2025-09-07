from z3 import *

def format_time(total_minutes):
    # total_minutes is minutes after midnight
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    # Create the Z3 solver instance
    solver = Solver()

    # We use an integer variable for the day:
    # 0 = Monday, 1 = Tuesday, 2 = Wednesday.
    day = Int("day")
    solver.add(Or(day == 0, day == 1, day == 2))

    # We represent the meeting start time as an integer (in minutes relative to 9:00).
    # Work day is 9:00 to 17:00. A 30-minute meeting means start must be in [0, 450]
    # because 0 means 9:00 and 450 means 9:00+450min=16:30, so the meeting will end at 17:00.
    start = Int("start")
    solver.add(start >= 0, start + 30 <= 480)

    # Pamela's stated preference is to avoid meetings before 16:00.
    # Since 9:00 corresponds to 0 in our time axis, 16:00 corresponds to 7 hours
    # later, i.e. 7*60 = 420 minutes after 9:00.
    solver.add(start >= 420)

    # Now we encode each participant's busy times by day.
    # We assume meeting intervals [start, start+30) do not overlap a busy interval.
    #
    # For Monday (day == 0):
    #   Amy has no meetings.
    #   Pamela is busy from 9:00 - 10:30 (i.e. [0, 90)) and 11:00 - 16:30 (i.e. [120,450)).
    #   Given Pamela’s later preference (start >=420), the morning slot is ruled out,
    #   and avoiding Pamela's busy [120,450) forces the meeting to occur after 16:30.
    #   Since start is in [0,450] and must be >=420, we must have start >= 450.
    solver.add(Implies(day == 0, start >= 450))

    # For Tuesday (day == 1):
    #   Amy is free.
    #   Pamela is busy from 9:00 - 9:30 ([0,30)) and 10:00 - 17:00 ([60,480)).
    #   Technically the only free slot is 9:30 to 10:00 ([30,60)),
    #   but Pamela's preference (start >= 420) rules that out.
    #   We therefore eliminate Tuesday as a possibility.
    solver.add(Implies(day == 1, False))

    # For Wednesday (day == 2):
    #   Amy is busy 11:00-11:30 ([120,150)) and 13:30-14:00 ([270,300)).
    #   Pamela is busy 9:00-9:30 ([0,30)), 10:00-11:00 ([60,120)),
    #     11:30-13:30 ([150,270)), 14:30-15:00 ([330,360)),
    #     and 16:00-16:30 ([420,450)).
    #   With Pamela’s preference start >=420, we again cannot start in [420,450)
    #   so start must be at least 450. Considering our upper bound, start ends up being 450.
    solver.add(Implies(day == 2, start >= 450))

    # Check if the constraints are satisfiable.
    if solver.check() == sat:
        model = solver.model()
        chosen_day = model[day].as_long()
        meeting_start_rel = model[start].as_long()   # minutes offset from 9:00
        meeting_end_rel = meeting_start_rel + 30

        # Convert relative times to actual clock time (minutes after midnight).
        # 9:00 is 9 * 60 = 540 minutes after midnight.
        actual_start = meeting_start_rel + 540
        actual_end = meeting_end_rel + 540

        # Map the integer day to a day name.
        day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
        day_str = day_map.get(chosen_day, "Unknown")

        # Format the meeting interval in HH:MM:HH:MM format.
        time_str = f"{format_time(actual_start)}:{format_time(actual_end)}"

        print(f"{day_str} {time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()