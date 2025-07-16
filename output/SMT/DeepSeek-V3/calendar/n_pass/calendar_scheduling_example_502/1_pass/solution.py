from z3 import *

def solve_scheduling():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    jack_busy = [
        (9 * 60 + 30, 10 * 60 + 30),
        (11 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 13 * 60),
        (14 * 60, 14 * 60 + 30),
        (16 * 60, 16 * 60 + 30)
    ]
    
    charlotte_busy = [
        (9 * 60 + 30, 10 * 60),
        (10 * 60 + 30, 12 * 60),
        (12 * 60 + 30, 13 * 60 + 30),
        (14 * 60, 16 * 60)
    ]

    def find_slot(preference_constraint=None):
        solver = Solver()
        start_time = Int('start_time')
        solver.add(start_time >= work_start)
        solver.add(start_time + meeting_duration <= work_end)
        if preference_constraint:
            solver.add(preference_constraint(start_time))
        for (busy_start, busy_end) in jack_busy:
            solver.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
        for (busy_start, busy_end) in charlotte_busy:
            solver.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
        if solver.check() == sat:
            model = solver.model()
            start = model[start_time].as_long()
            start_hh = start // 60
            start_mm = start % 60
            end = start + meeting_duration
            end_hh = end // 60
            end_mm = end % 60
            return (start_hh, start_mm, end_hh, end_mm)
        return None

    # First try to find a slot before 12:30
    slot = find_slot(lambda st: st <= 12 * 60)
    if slot is None:
        # If no slot found, try without the preference
        slot = find_slot()
    if slot is not None:
        start_hh, start_mm, end_hh, end_mm = slot
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()