from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define possible days
    days = ['Monday', 'Tuesday']
    day = Int('day')  # 0 for Monday, 1 for Tuesday

    # Constraint: day must be 0 or 1
    s.add(Or(day == 0, day == 1))

    # Define start and end times (in minutes from 9:00, i.e., 540 minutes is 9:00)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Meeting duration is 1 hour (60 minutes)
    s.add(end_time == start_time + 60)

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540)
    s.add(end_time <= 1020)

    # Patricia's busy slots in minutes from 9:00 for each day
    patricia_busy = {
        'Monday': [
            (10*60, 10*60 + 30),    # 10:00-10:30
            (11*60 + 30, 12*60),    # 11:30-12:00
            (13*60, 13*60 + 30),     # 13:00-13:30
            (14*60 + 30, 15*60 + 30), # 14:30-15:30
            (16*60, 16*60 + 30),     # 16:00-16:30
        ],
        'Tuesday': [
            (10*60, 10*60 + 30),    # 10:00-10:30
            (11*60, 12*60),          # 11:00-12:00
            (14*60, 16*60),          # 14:00-16:00
            (16*60 + 30, 17*60)      # 16:30-17:00
        ]
    }

    # Jesse's busy slots in minutes from 9:00 for each day
    jesse_busy = {
        'Monday': [
            (9*60, 17*60)  # 9:00-17:00 (entire day blocked)
        ],
        'Tuesday': [
            (11*60, 11*60 + 30),    # 11:00-11:30
            (12*60, 12*60 + 30),     # 12:00-12:30
            (13*60, 14*60),          # 13:00-14:00
            (14*60 + 30, 15*60),     # 14:30-15:00
            (15*60 + 30, 17*60)      # 15:30-17:00
        ]
    }

    # For each day, add constraints that the meeting does not overlap with any busy slots
    def add_day_constraints(day_idx, busy_slots_patricia, busy_slots_jesse):
        day_constraint = (day == day_idx)
        # Patricia's constraints for the day
        patricia_constraints = []
        for (busy_start, busy_end) in busy_slots_patricia:
            # Meeting is before or after the busy slot
            patricia_constraints.append(Or(
                end_time <= busy_start,
                start_time >= busy_end
            ))
        # Jesse's constraints for the day
        jesse_constraints = []
        for (busy_start, busy_end) in busy_slots_jesse:
            jesse_constraints.append(Or(
                end_time <= busy_start,
                start_time >= busy_end
            ))
        # Combine all constraints for the day
        s.add(Implies(day_constraint, And(And(patricia_constraints), And(jesse_constraints))))

    # Add constraints for Monday
    add_day_constraints(0, patricia_busy['Monday'], jesse_busy['Monday'])
    # Add constraints for Tuesday
    add_day_constraints(1, patricia_busy['Tuesday'], jesse_busy['Tuesday'])

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        day_idx = model[day].as_long()
        selected_day = days[day_idx]
        start_min = model[start_time].as_long()
        end_min = model[end_time].as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        start_time_str = minutes_to_time(start_min)
        end_time_str = minutes_to_time(end_min)

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {selected_day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()