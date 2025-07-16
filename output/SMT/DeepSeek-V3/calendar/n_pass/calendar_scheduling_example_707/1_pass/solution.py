from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days
    days = ['Monday', 'Tuesday', 'Wednesday']
    day = Int('day')
    s.add(day >= 0, day <= 2)  # 0: Monday, 1: Tuesday, 2: Wednesday

    # Define the start and end times (in minutes from 9:00)
    start_time = Int('start_time')
    end_time = Int('end_time')
    meeting_duration = 30  # minutes

    # Work hours are 9:00 to 17:00 (480 minutes from 9:00)
    s.add(start_time >= 0, end_time <= 480)
    s.add(end_time == start_time + meeting_duration)

    # Ryan cannot meet on Wednesday (day 2)
    s.add(day != 2)

    # Adam wants to avoid Monday before 14:30 (14:30 is 330 minutes from 9:00)
    # So if day is Monday (0), start_time must be >= 330
    s.add(Implies(day == 0, start_time >= 330))

    # Ryan's busy slots (in minutes from 9:00)
    ryan_busy = {
        0: [(30, 60), (120, 180), (240, 270), (390, 420)],  # Monday
        1: [(150, 210), (390, 420)],  # Tuesday
        2: [(180, 240), (390, 420), (450, 480)]  # Wednesday
    }

    # Adam's busy slots (in minutes from 9:00)
    adam_busy = {
        0: [(0, 90), (120, 270), (300, 420), (450, 480)],  # Monday
        1: [(0, 60), (90, 390), (420, 480)],  # Tuesday
        2: [(0, 30), (60, 120), (150, 330), (360, 390), (420, 450)]  # Wednesday
    }

    # Function to check if a time slot overlaps with any busy slots
    def is_busy(time_slot, busy_slots):
        start, end = time_slot
        for busy_start, busy_end in busy_slots:
            if Not(Or(end <= busy_start, start >= busy_end)):
                return True
        return False

    # Constraints for Ryan's availability
    ryan_available = True
    for day_idx, slots in ryan_busy.items():
        ryan_available = And(ryan_available, Implies(day == day_idx, Not(is_busy((start_time, end_time), slots))))
    s.add(ryan_available)

    # Constraints for Adam's availability
    adam_available = True
    for day_idx, slots in adam_busy.items():
        adam_available = And(adam_available, Implies(day == day_idx, Not(is_busy((start_time, end_time), slots))))
    s.add(adam_available)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_idx = m[day].as_long()
        start = m[start_time].as_long()
        end = m[end_time].as_long()

        # Convert start and end times to HH:MM format
        start_hh = 9 + start // 60
        start_mm = start % 60
        end_hh = 9 + end // 60
        end_mm = end % 60

        print("SOLUTION:")
        print(f"Day: {days[day_idx]}")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()