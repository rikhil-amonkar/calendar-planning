from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
    day = Int('day')
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 means 9:00, 30 means 9:30)
    end_time = Int('end_time')

    # Constraints for day: must be 0, 1, 2, or 3
    s.add(day >= 0, day <= 3)

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Meeting must be within 9:00 to 17:00 (540 to 1020 minutes in 24-hour format)
    s.add(start_time >= 0)  # 9:00 is 0 in our encoding (540 - 540)
    s.add(end_time <= 480)   # 17:00 is 480 (1020 - 540 = 480)

    # Mary's busy slots per day (each slot is (start, end) in minutes from 9:00)
    mary_schedule = {
        1: [(60, 90), (390, 420)],  # Tuesday: 10:00-10:30 (60-90), 15:30-16:00 (390-420)
        2: [(30, 60), (360, 390)],  # Wednesday: 9:30-10:00 (30-60), 15:00-15:30 (360-390)
        3: [(0, 60), (90, 150)],    # Thursday: 9:00-10:00 (0-60), 10:30-11:30 (90-150)
    }

    # Alexis's busy slots per day
    alexis_schedule = {
        0: [(0, 60), (90, 180), (210, 450)],  # Monday: 9:00-10:00, 10:30-12:00, 12:30-16:30
        1: [(0, 60), (90, 150), (180, 390), (420, 480)],  # Tuesday: 9:00-10:00, 10:30-11:30, 12:00-15:30, 16:00-17:00
        2: [(0, 120), (150, 480)],  # Wednesday: 9:00-11:00, 11:30-17:00
        3: [(60, 120), (300, 330), (390, 420), (450, 480)],  # Thursday: 10:00-12:00, 14:00-14:30, 15:30-16:00, 16:30-17:00
    }

    # Function to add constraints that the meeting does not overlap with any busy slots for a given day and schedule
    def add_no_overlap_constraints(day_var, start, end, schedule_dict):
        constraints = []
        for d in schedule_dict:
            slots = schedule_dict[d]
            for slot in slots:
                slot_start, slot_end = slot
                # If the meeting is on day d, it must not overlap with any slot in d
                constraints.append(Or(day_var != d,
                                    Not(And(start < slot_end, end > slot_start))))
        return constraints

    # Add no-overlap constraints for Mary and Alexis
    mary_constraints = add_no_overlap_constraints(day, start_time, end_time, mary_schedule)
    alexis_constraints = add_no_overlap_constraints(day, start_time, end_time, alexis_schedule)

    for c in mary_constraints:
        s.add(c)
    for c in alexis_constraints:
        s.add(c)

    # Find the earliest possible time: prioritize earlier days and earlier start times
    # We'll optimize by finding a solution, then iteratively asking for earlier times
    result = s.check()
    if result == sat:
        model = s.model()
        best_day = model[day].as_long()
        best_start = model[start_time].as_long()
        best_end = model[end_time].as_long()

        # Convert best_day to day name
        day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
        day_str = day_names[best_day]

        # Convert start and end times to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 is 540 minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = minutes_to_time(best_start)
        end_str = minutes_to_time(best_end)

        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()