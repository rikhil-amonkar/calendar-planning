# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Or

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    # Problem data
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy intervals are half-open [start, end)
    schedules = {
        "Lisa": [
            ("09:00", "10:00"),
            ("10:30", "11:30"),
            ("12:30", "13:00"),
            ("16:00", "16:30"),
        ],
        "Bobby": [
            ("09:00", "09:30"),
            ("10:00", "10:30"),
            ("11:30", "12:00"),
            ("15:00", "15:30"),
        ],
        "Randy": [
            ("09:30", "10:00"),
            ("10:30", "11:00"),
            ("11:30", "12:30"),
            ("13:00", "13:30"),
            ("14:30", "15:30"),
            ("16:00", "16:30"),
        ],
    }

    # Convert to minutes
    busy = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Z3 model
    opt = Optimize()
    start = Int("start")
    end = Int("end")

    # Hard constraints
    opt.add(end == start + duration)
    opt.add(start >= work_start)
    opt.add(end <= work_end)

    # No overlap with any busy interval for each participant
    for person, intervals in busy.items():
        for s, e in intervals:
            # Either the meeting ends before their busy slot starts, or starts after it ends
            opt.add(Or(end <= s, start >= e))

    # Preference: Bobby would like to avoid meetings after 15:00
    # Add as a soft constraint: prefer end <= 15:00
    fifteen = to_minutes("15:00")
    opt.add_soft(end <= fifteen, weight=1, id="avoid_after_15")

    # Tie-breaker: among equally preferred solutions, pick earliest start
    opt.minimize(start)

    if opt.check() != 1:  # sat == 1
        raise RuntimeError("No feasible schedule found (unexpected for this task).")

    model = opt.model()
    s_min = model.eval(start).as_long()
    e_min = model.eval(end).as_long()

    result = [
        "SOLUTION:",
        f"Day: {day}",
        f"Start Time: {to_hhmm(s_min)} (24-hour format)",
        f"End Time: {to_hhmm(e_min)} (24-hour format)",
    ]
    print("\n".join(result))

if __name__ == "__main__":
    schedule_meeting()