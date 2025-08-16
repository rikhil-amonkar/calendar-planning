from z3 import Solver, Int, Or, And, sat

def hhmm_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_hhmm(x):
    h = x // 60
    m = x % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    day = "Monday"
    work_start = hhmm_to_min("09:00")
    work_end = hhmm_to_min("17:00")
    meeting_duration = 60  # minutes

    # Busy schedules (inclusive of start, exclusive of end)
    schedules = {
        "Kayla": [("10:00", "10:30"), ("14:30", "16:00")],
        "Rebecca": [("09:00", "13:00"), ("13:30", "15:00"), ("15:30", "16:00")],
    }

    # Z3 variables
    start = Int("start")  # minutes from midnight
    end = Int("end")

    s = Solver()
    s.add(end == start + meeting_duration)
    s.add(And(start >= work_start, end <= work_end))

    # Add non-overlap constraints for each participant's busy intervals
    for person, intervals in schedules.items():
        for (b_start_str, b_end_str) in intervals:
            b_start = hhmm_to_min(b_start_str)
            b_end = hhmm_to_min(b_end_str)
            # Meeting [start, end) does not overlap busy [b_start, b_end)
            s.add(Or(end <= b_start, start >= b_end))

    if s.check() == sat:
        m = s.model()
        st = m[start].as_long()
        et = m[end].as_long()
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {min_to_hhmm(st)}")
        print(f"End Time: {min_to_hhmm(et)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    schedule_meeting()