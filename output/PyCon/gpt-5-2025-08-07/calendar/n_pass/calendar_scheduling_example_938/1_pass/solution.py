from constraint import Problem

# Meeting parameters
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes
MEETING_DURATION = 30
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Busy schedules in minutes since midnight
def t(h, m): return h * 60 + m

eugene_busy = {
    "Monday":    [(t(11,0), t(12,0)), (t(13,30), t(14,0)), (t(14,30), t(15,0)), (t(16,0), t(16,30))],
    "Wednesday": [(t(9,0), t(9,30)), (t(11,0), t(11,30)), (t(12,0), t(12,30)), (t(13,30), t(15,0))],
    "Thursday":  [(t(9,30), t(10,0)), (t(11,0), t(12,30))],
    "Friday":    [(t(10,30), t(11,0)), (t(12,0), t(12,30)), (t(13,0), t(13,30))],
}

eric_busy = {
    "Monday":    [(t(9,0), t(17,0))],
    "Tuesday":   [(t(9,0), t(17,0))],
    "Wednesday": [(t(9,0), t(11,30)), (t(12,0), t(14,0)), (t(14,30), t(16,30))],
    "Thursday":  [(t(9,0), t(17,0))],
    "Friday":    [(t(9,0), t(11,0)), (t(11,30), t(17,0))],
}

def overlaps(a_start, a_end, b_start, b_end):
    return not (a_end <= b_start or a_start >= b_end)

def is_free(busy_list, start, end):
    for bs, be in busy_list:
        if overlaps(start, end, bs, be):
            return False
    return True

# Build constraint problem
problem = Problem()
problem.addVariable("Day", DAYS)
problem.addVariable("Start", list(range(WORK_START, WORK_END - MEETING_DURATION + 1, 30)))

def availability_constraint(day, start):
    end = start + MEETING_DURATION
    if not (WORK_START <= start and end <= WORK_END):
        return False
    eb = eugene_busy.get(day, [])
    rb = eric_busy.get(day, [])
    return is_free(eb, start, end) and is_free(rb, start, end)

problem.addConstraint(availability_constraint, ("Day", "Start"))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Preference: avoid Wednesday if possible; then earliest day/time
day_rank = {d: i for i, d in enumerate(DAYS)}
def pref_key(sol):
    penalty = 0 if sol["Day"] != "Wednesday" else 1
    return (penalty, day_rank[sol["Day"]], sol["Start"])

best = min(solutions, key=pref_key)

def fmt_time(m):
    return f"{m//60:02d}:{m%60:02d}"

start = best["Start"]
end = start + MEETING_DURATION
day = best["Day"]

# Output includes day and time range in HH:MM:HH:MM within braces
print(f"{day} {{{fmt_time(start)}:{fmt_time(end)}}}")