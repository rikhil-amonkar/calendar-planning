from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (540 minutes in 24-hour format)
    end_time = Int('end_time')

    # Constraints for day: must be 0, 1, or 2
    s.add(Or(day == 0, day == 1, day == 2))

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes in 24-hour format)
    # Meeting duration is 1 hour (60 minutes)
    s.add(start_time >= 540)  # 9:00
    s.add(end_time == start_time + 60)
    s.add(end_time <= 1020)   # 17:00

    # Stephanie's existing meetings per day (each is a tuple of start and end in minutes from 0:00)
    stephanie_schedule = {
        0: [(570, 600), (630, 660), (690, 720), (840, 870)],  # Monday
        1: [(720, 780)],                                       # Tuesday
        2: [(540, 600), (780, 840)]                           # Wednesday
    }

    # Betty's existing meetings per day
    betty_schedule = {
        0: [(540, 600), (660, 690), (870, 900), (930, 960)],  # Monday
        1: [(540, 570), (690, 720), (750, 870), (930, 960)],  # Tuesday
        2: [(600, 690), (720, 840), (870, 1020)]              # Wednesday
    }

    # Constraint: The meeting does not overlap with any of Stephanie's meetings on the selected day
    def no_overlap_with_person(day_var, person_schedule):
        constraints = []
        for d, meetings in person_schedule.items():
            for (meet_start, meet_end) in meetings:
                # If the meeting is on day d, then the new meeting must not overlap
                constraints.append(
                    Implies(day_var == d,
                            Or(start_time >= meet_end,
                               end_time <= meet_start)
                    )
                )
        return constraints

    s.add(no_overlap_with_person(day, stephanie_schedule))
    s.add(no_overlap_with_person(day, betty_schedule))

    # Stephanie prefers to avoid Monday (day 0)
    s.add(day != 0)

    # Betty cannot meet on Tuesday after 12:30 (750 minutes from 0:00 is 12:30)
    # So on Tuesday, the meeting must end by 12:30 or start after 12:30 (but given meeting is 1 hour, start_time must be <= 750 - 60 = 690)
    s.add(Implies(day == 1, start_time + 60 <= 750))

    # Check for solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()

        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[day_val]

        # Convert start and end times from minutes to HH:MM format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(end_val)

        # Print solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()