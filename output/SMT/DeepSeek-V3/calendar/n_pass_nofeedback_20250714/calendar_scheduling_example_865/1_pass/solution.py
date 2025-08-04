from z3 import *

def solve_scheduling():
    # Create the solver with optimization
    opt = Optimize()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 means 9:00, 60 means 10:00)
    end_time = Int('end_time')

    # Constraints for day: must be 0, 1, 2, or 3
    opt.add(day >= 0)
    opt.add(day <= 3)

    # Meeting duration is 1 hour (60 minutes)
    opt.add(end_time == start_time + 60)

    # Work hours are 9:00 to 17:00 (480 minutes from 9:00)
    # So start_time must be >= 0 (9:00) and end_time <= 480 (17:00)
    opt.add(start_time >= 0)
    opt.add(end_time <= 480)

    # Megan's busy slots per day in minutes from 9:00
    megan_busy = {
        0: [(4*60, 4*60 + 30), (5*60, 5*60 + 90)],  # Monday: 13:00-13:30 (4h from 9:00 is 13:00), 14:00-15:30
        1: [(0, 30), (3*60, 3*60 + 30), (7*60, 8*60)],  # Tuesday: 9:00-9:30, 12:00-12:30, 16:00-17:00
        2: [(30, 60), (90, 150), (210, 300), (7*60, 7*60 + 30)],  # Wednesday: 9:30-10:00, 10:30-11:30, 12:30-14:00, 16:00-16:30
        3: [(4*60 + 30, 5*60 + 30), (6*60, 6*60 + 30)]  # Thursday: 13:30-14:30, 15:00-15:30
    }

    # Daniel's busy slots per day in minutes from 9:00
    daniel_busy = {
        0: [(60, 150), (210, 360)],  # Monday: 10:00-11:30, 12:30-15:00
        1: [(0, 60), (90, 8*60)],  # Tuesday: 9:00-10:00, 10:30-17:00
        2: [(0, 60), (90, 150), (180, 8*60)],  # Wednesday: 9:00-10:00, 10:30-11:30, 12:00-17:00
        3: [(0, 180), (210, 330), (360, 390), (7*60, 8*60)]  # Thursday: 9:00-12:00, 12:30-14:30, 15:00-15:30, 16:00-17:00
    }

    # Function to add no-overlap constraints for a person's busy slots
    def add_no_overlap(day_var, start, end, busy_slots_dict):
        # For each day, if the meeting is on that day, it must not overlap with any busy slot
        for d in busy_slots_dict:
            for (busy_start, busy_end) in busy_slots_dict[d]:
                opt.add(Not(And(day_var == d,
                               Not(Or(end <= busy_start, start >= busy_end)))))

    add_no_overlap(day, start_time, end_time, megan_busy)
    add_no_overlap(day, start_time, end_time, daniel_busy)

    # Objective: minimize start_time
    opt.minimize(start_time + day * 480)  # prioritize earlier days and times

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = m[end_time].as_long()

        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_name = days[day_val]

        # Convert start and end times from minutes to HH:MM
        def minutes_to_time(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(end_val)

        # Prepare the solution output
        solution = f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}"
        return solution
    else:
        return "No solution found."

print(solve_scheduling())