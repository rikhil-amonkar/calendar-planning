from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_h = Int('start_h')
    start_m = Int('start_m')
    end_h = Int('end_h')
    end_m = Int('end_m')

    # Meeting duration is 30 minutes
    s.add(end_h == start_h)
    s.add(end_m == start_m + 30)

    # Handle minute overflow (e.g., 13:30 + 30 mins = 14:00)
    s.add(Or(
        And(end_m == 30, start_m == 0),
        And(end_m == 60, start_m == 30)
    ))
    s.add(end_m <= 60)

    # Working hours are 9:00 to 17:00
    s.add(start_h >= 9)
    s.add(end_h <= 17)
    s.add(Or(start_h < 17, And(start_h == 17, start_m == 0)))  # 17:00 is the last possible start time (for 30 min meeting)

    # Day constraints (0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday)
    s.add(day >= 0, day <= 3)

    # Cheryl's calendar is wide open, but she prefers not Wednesday (2) or Thursday (3)
    # We'll add a soft constraint to avoid Wednesday and Thursday if possible
    # First, try without Wednesday and Thursday
    temp_solver = Solver()
    temp_solver.add(day != 2, day != 3)
    # Copy all other constraints to temp_solver
    for c in s.assertions():
        temp_solver.add(c)

    # James's busy slots per day
    james_busy = {
        0: [(9, 0, 9, 30), (10, 30, 11, 0), (12, 30, 13, 0), (14, 30, 15, 30), (16, 30, 17, 0)],
        1: [(9, 0, 11, 0), (11, 30, 12, 0), (12, 30, 15, 30), (16, 0, 17, 0)],
        2: [(10, 0, 11, 0), (12, 0, 13, 0), (13, 30, 16, 0)],
        3: [(9, 30, 11, 30), (12, 0, 12, 30), (13, 0, 13, 30), (14, 0, 14, 30), (16, 30, 17, 0)]
    }

    # Function to check if the meeting overlaps with any busy slot
    def no_overlap(d, sh, sm, eh, em):
        conditions = []
        for busy in james_busy.get(d, []):
            bs_h, bs_m, be_h, be_m = busy
            # Meeting does not overlap with busy slot if:
            # Meeting ends before busy starts or meeting starts after busy ends
            conditions.append(Or(
                eh < bs_h,
                And(eh == bs_h, em <= bs_m),
                sh > be_h,
                And(sh == be_h, sm >= be_m)
            ))
        return And(conditions) if conditions else True

    s.add(If(day == 0, no_overlap(0, start_h, start_m, end_h, end_m),
          If(day == 1, no_overlap(1, start_h, start_m, end_h, end_m),
          If(day == 2, no_overlap(2, start_h, start_m, end_h, end_m),
          no_overlap(3, start_h, start_m, end_h, end_m)))))

    # Try to find a solution avoiding Wednesday and Thursday first
    if temp_solver.check() == sat:
        m = temp_solver.model()
        selected_day = m[day].as_long()
    else:
        # If no solution without Wednesday or Thursday, try including them
        if s.check() == sat:
            m = s.model()
            selected_day = m[day].as_long()
        else:
            return "No solution found"

    # Now, find the earliest time on the selected day
    # We'll iterate through possible times in order to find the earliest
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    busy_slots = james_busy.get(selected_day, [])
    busy_slots.sort()  # Sort by start time

    # Generate all possible 30-minute slots in the day
    possible_slots = []
    for h in range(9, 17):
        for m in [0, 30]:
            if h == 16 and m == 30:
                continue  # 16:30-17:00 is the last possible slot
            slot_start = (h, m)
            slot_end = (h, m + 30) if m == 0 else (h + 1, 0)
            possible_slots.append((slot_start, slot_end))

    # Filter out slots that overlap with James's busy times
    available_slots = []
    for (sh, sm), (eh, em) in possible_slots:
        overlap = False
        for (bs_h, bs_m, be_h, be_m) in busy_slots:
            if not (eh < bs_h or (eh == bs_h and em <= bs_m) or
                    sh > be_h or (sh == be_h and sm >= be_m)):
                overlap = True
                break
        if not overlap:
            available_slots.append((sh, sm, eh, em))

    if not available_slots:
        return "No solution found"

    # Select the earliest available slot
    sh, sm, eh, em = available_slots[0]

    # Prepare the solution
    solution = f"SOLUTION:\nDay: {day_names[selected_day]}\nStart Time: {sh:02d}:{sm:02d}\nEnd Time: {eh:02d}:{em:02d}"
    return solution

print(solve_scheduling())