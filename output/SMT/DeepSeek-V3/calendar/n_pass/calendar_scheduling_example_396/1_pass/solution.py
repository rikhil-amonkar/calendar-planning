from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Meeting duration is 30 minutes
    duration = 30

    # Define start time in minutes from 9:00 (540 minutes from midnight)
    start_time = Int('start_time')
    # Total minutes in work hours: 9:00 to 17:00 is 8 hours = 480 minutes
    min_time = 9 * 60  # 9:00 in minutes
    max_time = 17 * 60 - duration  # 17:00 - 30 minutes = 16:30 in minutes

    # Constraint: start_time must be within work hours considering duration
    s.add(start_time >= min_time)
    s.add(start_time <= max_time)

    # Each participant's busy slots in minutes (start, end)
    # Format: list of (start_minute, end_minute) pairs
    andrea_busy = []  # Andrea is free all day
    jack_busy = [(9*60, 9*60 + 30), (14*60, 14*60 + 30)]
    madison_busy = [(9*60 + 30, 10*60 + 30), (13*60, 14*60), (15*60, 15*60 + 30), (16*60 + 30, 17*60)]
    rachel_busy = [(9*60 + 30, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 13*60 + 30), (14*60 + 30, 15*60 + 30), (16*60, 17*60)]
    douglas_busy = [(9*60, 11*60 + 30), (12*60, 16*60 + 30)]
    ryan_busy = [(9*60, 9*60 + 30), (13*60, 14*60), (14*60 + 30, 17*60)]

    # Function to add constraints for a participant's busy slots
    def add_participant_constraints(busy_slots):
        constraints = []
        for (busy_start, busy_end) in busy_slots:
            # The meeting does not overlap with the busy slot: it's either entirely before or entirely after
            constraint = Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            )
            constraints.append(constraint)
        # All constraints must be satisfied (i.e., no overlap with any busy slot)
        if constraints:
            s.add(And(*constraints))

    # Add constraints for each participant
    add_participant_constraints(andrea_busy)
    add_participant_constraints(jack_busy)
    add_participant_constraints(madison_busy)
    add_participant_constraints(rachel_busy)
    add_participant_constraints(douglas_busy)
    add_participant_constraints(ryan_busy)

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start_time].as_long()
        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_minutes + duration
        end_hours = end_minutes // 60
        end_min = end_minutes % 60
        end_str = f"{end_hours:02d}:{end_min:02d}"
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()