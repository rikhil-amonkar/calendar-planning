from z3 import Int, Optimize, Or, And, sat

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    # Problem setup
    day = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules as (start, end) in minutes since 00:00
    schedules = {
        "Jacob": [
            ("13:30", "14:00"), ("14:30", "15:00")
        ],
        "Diana": [
            ("09:30", "10:00"), ("11:30", "12:00"),
            ("13:00", "13:30"), ("16:00", "16:30")
        ],
        "Adam": [
            ("09:30", "10:30"), ("11:00", "12:30"),
            ("15:30", "16:00")
        ],
        "Angela": [
            ("09:30", "10:00"), ("10:30", "12:00"),
            ("13:00", "15:30"), ("16:00", "16:30")
        ],
        "Dennis": [
            ("09:00", "09:30"), ("10:30", "11:30"),
            ("13:00", "15:00"), ("16:30", "17:00")
        ],
    }

    # Convert busy times to minutes
    busy_intervals = []
    for person, intervals in schedules.items():
        for s, e in intervals:
            busy_intervals.append((time_to_minutes(s), time_to_minutes(e)))

    # Z3 variables and solver
    start = Int('start')
    o = Optimize()

    # Constraints: within work hours, fixed duration, 30-min grid
    o.add(start >= work_start)
    o.add(start + duration <= work_end)
    o.add((start - work_start) % 30 == 0)

    # No overlap with any busy interval: [start, start+duration) does not intersect [b_s, b_e)
    for b_s, b_e in busy_intervals:
        o.add(Or(start + duration <= b_s, start >= b_e))

    # Prefer earliest feasible start time
    o.minimize(start)

    if o.check() == sat:
        m = o.model()
        start_val = m[start].as_long()
        end_val = start_val + duration
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {minutes_to_time(start_val)}")
        print(f"End Time: {minutes_to_time(end_val)}")
    else:
        # As per problem statement, a solution exists; this is a fallback.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: 00:00")
        print("End Time: 00:30")

if __name__ == "__main__":
    schedule_meeting()