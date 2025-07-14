from z3 import *

def solve_scheduling():
    # Define the days and work hours
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Define the busy slots for Nicole and Daniel in minutes since midnight
    nicole_busy = {
        "Tuesday": [(16 * 60, 16 * 60 + 30)],
        "Wednesday": [(15 * 60, 15 * 60 + 30)],
        "Friday": [(12 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]
    }
    
    daniel_busy = {
        "Monday": [(9 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 16 * 60 + 30)],
        "Tuesday": [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), 
                    (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
        "Wednesday": [(9 * 60, 10 * 60), (11 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), 
                     (14 * 60, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],
        "Thursday": [(11 * 60, 12 * 60), (13 * 60, 14 * 60), (15 * 60, 15 * 60 + 30)],
        "Friday": [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 14 * 60 + 30), 
                   (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    }

    # Initialize Z3 solver
    s = Solver()

    # Variables: day (as an index), start time in minutes since midnight
    day = Int('day')
    start_time = Int('start_time')

    # Constraints for day and start time
    s.add(day >= 0, day < len(days))
    s.add(start_time >= work_start, start_time + meeting_duration <= work_end)

    # Function to check if a time slot is free for a person
    def is_free(busy_slots, day_name, start, duration):
        constraints = []
        for (busy_start, busy_end) in busy_slots.get(day_name, []):
            constraints.append(Or(start + duration <= busy_start, start >= busy_end))
        return And(*constraints) if constraints else True

    # For each possible day, add constraints that the slot is free for both
    day_constraints = []
    for i, day_name in enumerate(days):
        nicole_free = is_free(nicole_busy, day_name, start_time, meeting_duration)
        daniel_free = is_free(daniel_busy, day_name, start_time, meeting_duration)
        day_constraints.append(And(day == i, nicole_free, daniel_free))

    s.add(Or(*day_constraints))

    # Find the earliest possible solution by minimizing start_time
    s.push()
    s.minimize(start_time)
    if s.check() == sat:
        m = s.model()
        chosen_day = days[m[day].as_long()]
        chosen_start = m[start_time].as_long()
        chosen_end = chosen_start + meeting_duration
        # Convert minutes back to HH:MM format
        start_hh = chosen_start // 60
        start_mm = chosen_start % 60
        end_hh = chosen_end // 60
        end_mm = chosen_end % 60
        print(f"SOLUTION:")
        print(f"Day: {chosen_day}")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()