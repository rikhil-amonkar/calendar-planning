from z3 import *

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60
WORK_END = 17 * 60

# Days: 0=Monday, 1=Tuesday, 2=Wednesday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}

# Busy schedules (start, end) in minutes from 00:00
ryan_busy = {
    0: [(9*60+30, 10*60), (11*60, 12*60), (13*60, 13*60+30), (15*60+30, 16*60)],
    1: [(11*60+30, 12*60+30), (15*60+30, 16*60)],
    2: [(12*60, 13*60), (15*60+30, 16*60), (16*60+30, 17*60)],
}
adam_busy = {
    0: [(9*60, 10*60+30), (11*60, 13*60+30), (14*60, 16*60), (16*60+30, 17*60)],
    1: [(9*60, 10*60), (10*60+30, 15*60+30), (16*60, 17*60)],
    2: [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
}

def no_overlap_constraints(day_var, start_var, end_var, busy_map):
    cons = []
    for d, intervals in busy_map.items():
        # Meeting must not overlap any busy interval on day d
        day_cons = []
        for (s, e) in intervals:
            day_cons.append(Or(end_var <= s, start_var >= e))
        if day_cons:
            cons.append(Implies(day_var == d, And(*day_cons)))
        else:
            cons.append(Implies(day_var == d, True))
    return cons

def fmt_time(m):
    return f"{m//60:02d}:{m%60:02d}"

def main():
    day = Int('day')      # 0=Mon,1=Tue,2=Wed
    start = Int('start')  # minutes since 00:00
    end = start + DURATION

    opt = Optimize()

    # Hard constraints
    opt.add(day >= 0, day <= 2)
    opt.add(start >= WORK_START, end <= WORK_END)
    opt.add(start % 30 == 0)  # align to 30-minute boundaries
    # Ryan cannot meet on Wednesday
    opt.add(day != 2)

    # Non-overlap for each participant
    opt.add(*no_overlap_constraints(day, start, end, ryan_busy))
    opt.add(*no_overlap_constraints(day, start, end, adam_busy))

    # Soft preferences:
    # 1) Prefer Tuesday
    opt.add_soft(day == 1, weight="2")
    # 2) If Monday, prefer at/after 14:30
    opt.add_soft(Or(day != 0, start >= 14*60 + 30), weight="1")

    if opt.check() != sat:
        print("No feasible meeting time found.")
        return

    model = opt.model()
    d = model[day].as_long()
    s = model[start].as_long()
    e = s + DURATION

    print(f"{day_names[d]} {{{fmt_time(s)}:{fmt_time(e)}}}")

if __name__ == "__main__":
    main()