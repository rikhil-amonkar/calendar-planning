#!/usr/bin/env python3
import z3

def schedule_meeting():
    # Meeting duration is 30 minutes.
    MEETING_DURATION = 30

    # Workday runs from 09:00 to 17:00.
    WORK_START = 9 * 60         # 09:00 = 540 minutes
    WORK_END   = 17 * 60        # 17:00 = 1020 minutes

    # Define day codes.
    MONDAY = 0
    TUESDAY = 1

    # Create a Z3 solver instance.
    solver = z3.Solver()

    # Define two variables:
    #   start : meeting start time (minutes from midnight)
    #   day   : which day the meeting is scheduled (0 for Monday, 1 for Tuesday)
    start = z3.Int("start")
    day   = z3.Int("day")

    # The meeting must start within work hours.
    solver.add(start >= WORK_START, start <= WORK_END - MEETING_DURATION)

    # The meeting must be on either Monday or Tuesday.
    solver.add(z3.Or(day == MONDAY, day == TUESDAY))

    # ----- Monday constraints -----
    # Harold is busy on Monday:
    #   • 09:00–10:00 busy
    #   • 10:30–17:00 busy
    # Thus the only free slot is exactly from 10:00 to 10:30.
    monday_slot = z3.And(start >= 10 * 60, start + MEETING_DURATION <= 10 * 60 + 30)
    solver.add(z3.Implies(day == MONDAY, monday_slot))

    # ----- Tuesday constraints -----
    # On Tuesday Harold is busy during:
    #   • 09:00–9:30, 10:30–11:30, 12:30–13:30, 14:30–15:30, and 16:00–17:00.
    # Although several free gaps exist (e.g. 9:30–10:30, 11:30–12:30, 13:30–14:30),
    # he would like to avoid any meeting that starts before 14:30.
    # This leaves the available/preferred slot from 15:30–16:00.
    tuesday_slot = z3.And(start >= 15 * 60 + 30, start + MEETING_DURATION <= 16 * 60)
    solver.add(z3.Implies(day == TUESDAY, tuesday_slot))

    # ----- Try Tuesday first (preferred) -----
    solver.push()  # Save the current constraints.
    solver.add(day == TUESDAY)
    if solver.check() == z3.sat:
        model = solver.model()
        chosen_day = model[day].as_long()
        chosen_start = model[start].as_long()
        solver.pop()  # Done with the Tuesday branch.
    else:
        # Tuesday wasn’t possible; try Monday.
        solver.pop()  # Undo the add(day == TUESDAY) constraint.
        solver.add(day == MONDAY)
        if solver.check() == z3.sat:
            model = solver.model()
            chosen_day = model[day].as_long()
            chosen_start = model[start].as_long()
        else:
            print("No valid meeting time could be found.")
            return

    meeting_end = chosen_start + MEETING_DURATION

    def minutes_to_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    day_str = "Monday" if chosen_day == MONDAY else "Tuesday"
    start_str = minutes_to_str(chosen_start)
    end_str   = minutes_to_str(meeting_end)
    print(f"Meeting scheduled on {day_str} from {start_str} to {end_str}")

if __name__ == "__main__":
    schedule_meeting()