from z3 import *

def solve_meeting():
    # Time constants
    WORK_START = 9 * 60
    WORK_END = 17 * 60
    DURATION = 30
    OFFSET = WORK_START  # base at 9:00
    MAX_OFFSET = WORK_END - WORK_START

    # Map day indices to names
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}

    # Busy intervals per person per day as (start_offset, end_offset) in minutes from 9:00
    # 9:00->0, 9:30->30, ..., 17:00->480
    betty_busy = {
        0: [(60, 90), (270, 300), (360, 390), (420, 450)],                 # Monday
        1: [(0, 30), (150, 180), (210, 240), (270, 300), (450, 480)],      # Tuesday
        2: [(30, 90), (240, 270), (300, 330)],                             # Wednesday
        3: [(30, 60), (150, 180), (300, 330), (360, 390), (450, 480)],     # Thursday
    }
    scott_busy = {
        0: [(30, 360), (390, 420), (450, 480)],                            # Monday
        1: [(0, 30), (60, 120), (150, 180), (210, 270), (300, 360), (420, 450)],  # Tuesday
        2: [(30, 210), (240, 270), (300, 330), (360, 390), (420, 450)],    # Wednesday
        3: [(0, 30), (60, 90), (120, 180), (210, 240), (360, 420), (450, 480)],   # Thursday
    }

    # Z3 variables
    day = Int('day')            # 0=Mon, 1=Tue, 2=Wed, 3=Thu
    start = Int('start')        # minutes offset from 9:00
    end = Int('end')            # start + 30

    opt = Optimize()

    # Domain constraints
    opt.add(day >= 0, day <= 3)
    opt.add(start >= 0, start <= MAX_OFFSET - DURATION)
    opt.add(end == start + DURATION)
    opt.add(end <= MAX_OFFSET)
    opt.add(start % 30 == 0)  # meeting starts on half-hour grid

    # No-overlap constraints for each participant per selected day
    def no_overlap(s, e):
        return Or(end <= s, start >= e)  # [start,end) does not intersect [s,e)

    for d in range(4):
        for (s, e) in betty_busy[d]:
            opt.add(Implies(day == d, no_overlap(s, e)))
        for (s, e) in scott_busy[d]:
            opt.add(Implies(day == d, no_overlap(s, e)))

    # Additional hard constraints from the problem statement:
    # Betty cannot meet on Monday or Tuesday
    opt.add(day != 0)  # no Monday
    opt.add(day != 1)  # no Tuesday
    # Betty cannot meet on Thursday before 15:00
    opt.add(Implies(day == 3, start >= (15 - 9) * 60))  # start >= 360

    # Preference: Scott would like to avoid Wednesday (soft constraint)
    opt.add_soft(day != 2)

    # Solve
    if opt.check() != sat:
        raise RuntimeError("No feasible schedule found.")
    model = opt.model()

    d = model[day].as_long()
    s = model[start].as_long()
    e = model[end].as_long()

    def to_hhmm(offset_minutes):
        total = OFFSET + offset_minutes
        hh = total // 60
        mm = total % 60
        return f"{hh:02d}:{mm:02d}"

    print("SOLUTION:")
    print(f"Day: {day_names[d]}")
    print(f"Start Time: {to_hhmm(s)} (24-hour format)")
    print(f"End Time: {to_hhmm(e)} (24-hour format)")

if __name__ == "__main__":
    solve_meeting()