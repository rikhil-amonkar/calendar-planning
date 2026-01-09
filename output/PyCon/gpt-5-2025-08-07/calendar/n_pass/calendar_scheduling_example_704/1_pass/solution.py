from constraint import Problem, AllEqualConstraint

# Meeting parameters
MEETING_DURATION_MIN = 30
WORK_START = (9 * 60)   # 09:00 in minutes
WORK_END = (17 * 60)    # 17:00 in minutes
DAYS = ["Monday", "Tuesday", "Wednesday"]

# Participants and their busy schedules (minutes from 00:00)
busy = {
    "Larry": {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": []
    },
    "Samuel": {
        "Monday": [
            (10*60 + 30, 11*60),      # 10:30-11:00
            (12*60, 12*60 + 30),      # 12:00-12:30
            (13*60, 15*60),           # 13:00-15:00
            (15*60 + 30, 16*60 + 30)  # 15:30-16:30
        ],
        "Tuesday": [
            (9*60, 12*60),            # 09:00-12:00
            (14*60, 15*60 + 30),      # 14:00-15:30
            (16*60 + 30, 17*60)       # 16:30-17:00
        ],
        "Wednesday": [
            (10*60 + 30, 11*60),      # 10:30-11:00
            (11*60 + 30, 12*60),      # 11:30-12:00
            (12*60 + 30, 13*60),      # 12:30-13:00
            (14*60, 14*60 + 30),      # 14:00-14:30
            (15*60, 16*60)            # 15:00-16:00
        ]
    }
}

# Preferences (soft): lower is better
# Larry prefers not Wednesday; Samuel prefers not Tuesday
day_penalty = {
    "Larry": {"Monday": 0, "Tuesday": 0, "Wednesday": 1},
    "Samuel": {"Monday": 0, "Tuesday": 1, "Wednesday": 0}
}
day_order = {"Monday": 0, "Tuesday": 1, "Wednesday": 2}

def overlaps(a_start, a_end, b_start, b_end):
    return not (a_end <= b_start or b_end <= a_start)

def generate_slots_for_day(day):
    slots = []
    t = WORK_START
    while t + MEETING_DURATION_MIN <= WORK_END:
        slots.append((day, t))
        t += 30  # half-hour increments
    return slots

def slot_is_free(participant, day, start_min):
    end_min = start_min + MEETING_DURATION_MIN
    for b_start, b_end in busy[participant][day]:
        if overlaps(start_min, end_min, b_start, b_end):
            return False
    return True

# Build domains per participant (day, start_minute) pairs they can attend
domains = {p: [] for p in busy.keys()}
for p in busy.keys():
    for d in DAYS:
        for (day, start_min) in generate_slots_for_day(d):
            if slot_is_free(p, day, start_min):
                domains[p].append((day, start_min))

# Use python-constraint to require everyone picks the same slot
problem = Problem()
for p in domains:
    problem.addVariable(p, domains[p])
problem.addConstraint(AllEqualConstraint())

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting slot found.")

# Choose the best slot:
# 1) Minimize sum of preference penalties
# 2) Then earliest day (Mon<Tue<Wed)
# 3) Then earliest time
def score_solution(sol):
    # All values equal, pick any
    (day, start_min) = next(iter(sol.values()))
    penalty_sum = sum(day_penalty[p][day] for p in sol.keys())
    return (penalty_sum, day_order[day], start_min)

best_sol = min(solutions, key=score_solution)
best_day, best_start = next(iter(best_sol.values()))
best_end = best_start + MEETING_DURATION_MIN

def fmt_time(m):
    h = m // 60
    s = m % 60
    return f"{h:02d}:{s:02d}"

start_str = fmt_time(best_start)
end_str = fmt_time(best_end)

# Output: time range in format HH:MM:HH:MM and the day of the week
print(f"{{{start_str}:{end_str}}}")
print(best_day)