from constraint import Problem

# Meeting parameters
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes
DURATION = 30         # 30 minutes
DAYS = ["Monday", "Tuesday", "Wednesday"]

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def overlap(a_start, a_end, b_start, b_end):
    return not (a_end <= b_start or b_end <= a_start)

# Busy schedules (inclusive of start, exclusive of end)
busy = {
    "Amy": {
        "Wednesday": [(to_minutes("11:00"), to_minutes("11:30")),
                      (to_minutes("13:30"), to_minutes("14:00"))],
    },
    "Pamela": {
        "Monday":    [(to_minutes("09:00"), to_minutes("10:30")),
                      (to_minutes("11:00"), to_minutes("16:30"))],
        "Tuesday":   [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("10:00"), to_minutes("17:00"))],
        "Wednesday": [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("10:00"), to_minutes("11:00")),
                      (to_minutes("11:30"), to_minutes("13:30")),
                      (to_minutes("14:30"), to_minutes("15:00")),
                      (to_minutes("16:00"), to_minutes("16:30"))],
    }
}

# Generate domain of all possible 30-minute slots within work hours for all days
domain = []
start_time = WORK_START
while start_time + DURATION <= WORK_END:
    for day in DAYS:
        domain.append((day, start_time))
    start_time += DURATION

# Set up constraint problem
problem = Problem()
problem.addVariable("slot", domain)

def is_free(participant, day, start):
    intervals = busy.get(participant, {}).get(day, [])
    meeting_start = start
    meeting_end = start + DURATION
    for b_start, b_end in intervals:
        if overlap(meeting_start, meeting_end, b_start, b_end):
            return False
    return True

# Both Amy and Pamela must be free
problem.addConstraint(lambda s: is_free("Amy", s[0], s[1]), ("slot",))
problem.addConstraint(lambda s: is_free("Pamela", s[0], s[1]), ("slot",))

solutions = problem.getSolutions()

# Preference handling:
# Pamela would like to avoid more meetings on:
# - Monday (avoid)
# - Tuesday (avoid)
# - Wednesday before 16:00 (avoid)
def preference_score(day, start):
    score = 0
    if day == "Monday":
        score -= 100
    if day == "Tuesday":
        score -= 100
    if day == "Wednesday":
        if start < to_minutes("16:00"):
            score -= 10
        else:
            score += 10  # prefer after 16:00 on Wednesday
    return score

# Choose the best solution according to preferences
best = None
best_score = None
for sol in solutions:
    day, start = sol["slot"]
    score = preference_score(day, start)
    if best is None or score > best_score or (score == best_score and (day, start) < (best[0], best[1])):
        best = (day, start)
        best_score = score

# Output the result: day and {HH:MM:HH:MM}
if best is None:
    raise RuntimeError("No feasible meeting time found.")
day, start = best
end = start + DURATION
print(day)
print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")