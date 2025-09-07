from z3 import *

def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    # Constants
    MONDAY = "Monday"
    WORK_START = 9 * 60
    WORK_END = 17 * 60
    MEETING_DURATION = 30
    EVELYN_LATEST_END = 13 * 60  # "do not want to meet after 13:00" => meeting ends by 13:00

    # Randy's busy intervals on Monday (in minutes since 00:00), half-open [start, end)
    randy_busy = [
        (9 * 60, 10 * 60 + 30),   # 09:00-10:30
        (11 * 60, 15 * 60 + 30),  # 11:00-15:30
        (16 * 60, 17 * 60),       # 16:00-17:00
    ]

    # Z3 variables
    start = Int('start')
    end = Int('end')

    s = Solver()

    # Basic meeting window constraints (within work hours)
    s.add(start >= WORK_START)
    s.add(end == start + MEETING_DURATION)
    s.add(end <= WORK_END)

    # Evelyn's preference: not after 13:00 (meeting must end by 13:00)
    s.add(end <= EVELYN_LATEST_END)

    # Randy's busy constraints: meeting must not overlap any busy interval
    for (b_start, b_end) in randy_busy:
        s.add(Or(end <= b_start, start >= b_end))

    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        end_val = m[end].as_long()
        time_range = f"{{{minutes_to_hhmm(start_val)}:{minutes_to_hhmm(end_val)}}}"
        print(time_range)
        print(MONDAY)
    else:
        print("No feasible time found")

if __name__ == "__main__":
    main()