# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

# Time utilities
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Build busy schedules (in minutes from midnight)
def build_schedule():
    def rng(s, e):  # inclusive start, exclusive end
        return (to_minutes(s), to_minutes(e))

    daniel = {
        "Monday":    [rng("09:30","10:30"), rng("12:00","12:30"), rng("13:00","14:00"),
                      rng("14:30","15:00"), rng("15:30","16:00")],
        "Tuesday":   [rng("11:00","12:00"), rng("13:00","13:30"),
                      rng("15:30","16:00"), rng("16:30","17:00")],
        "Wednesday": [rng("09:00","10:00"), rng("14:00","14:30")],
        "Thursday":  [rng("10:30","11:00"), rng("12:00","13:00"),
                      rng("14:30","15:00"), rng("15:30","16:00")],
        "Friday":    [rng("09:00","09:30"), rng("11:30","12:00"),
                      rng("13:00","13:30"), rng("16:30","17:00")],
    }

    bradley = {
        "Monday":    [rng("09:30","11:00"), rng("11:30","12:00"),
                      rng("12:30","13:00"), rng("14:00","15:00")],
        "Tuesday":   [rng("10:30","11:00"), rng("12:00","13:00"),
                      rng("13:30","14:00"), rng("15:30","16:30")],
        "Wednesday": [rng("09:00","10:00"), rng("11:00","13:00"),
                      rng("13:30","14:00"), rng("14:30","17:00")],
        "Thursday":  [rng("09:00","12:30"), rng("13:30","14:00"),
                      rng("14:30","15:00"), rng("15:30","16:30")],
        "Friday":    [rng("09:00","09:30"), rng("10:00","12:30"),
                      rng("13:00","13:30"), rng("14:00","14:30"),
                      rng("15:30","16:30")],
    }
    return daniel, bradley

def overlaps(a_start, a_end, b_start, b_end):
    return not (a_end <= b_start or a_start >= b_end)

def is_free(day, start, duration, busy):
    end = start + duration
    for (bs, be) in busy.get(day, []):
        if overlaps(start, end, bs, be):
            return False
    return True

def main():
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    step = 30  # minutes
    duration = 30

    daniel_busy, bradley_busy = build_schedule()

    # Preferences/constraints
    # Daniel would rather not (treated as hard constraints here): Wednesday, Thursday
    daniel_disallowed_days = {"Wednesday", "Thursday"}
    # Bradley does not want: Monday, Friday, and Tuesday before 12:00
    bradley_disallowed_days = {"Monday", "Friday"}
    tuesday_not_before = to_minutes("12:00")

    # Set up CSP
    problem = Problem()
    problem.addVariable("day", days)
    start_times = list(range(work_start, work_end - duration + 1, step))
    problem.addVariable("start", start_times)

    def constraint_ok(day, start):
        end = start + duration

        # Work hours
        if not (work_start <= start and end <= work_end):
            return False

        # Day preferences
        if day in daniel_disallowed_days:
            return False
        if day in bradley_disallowed_days:
            return False
        if day == "Tuesday" and start < tuesday_not_before:
            return False

        # Availability (no overlaps with busy times)
        if not is_free(day, start, duration, daniel_busy):
            return False
        if not is_free(day, start, duration, bradley_busy):
            return False

        return True

    problem.addConstraint(constraint_ok, ["day", "start"])

    solutions = problem.getSolutions()
    if not solutions:
        print("No feasible time found.")
        return

    # Pick earliest by day order then start time
    day_index = {d: i for i, d in enumerate(days)}
    best = sorted(solutions, key=lambda s: (day_index[s["day"]], s["start"]))[0]

    day = best["day"]
    start = best["start"]
    end = start + duration

    # Output must include the day and the time range like {HH:MM:HH:MM}
    time_range = f"{{{fmt_minutes(start)}:{fmt_minutes(end)}}}"
    print(f"{day} {time_range}")

if __name__ == "__main__":
    main()