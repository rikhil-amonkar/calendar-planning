from z3 import *

# Define meetings: (id, duration, value, available_start, available_end, recurrence)
meetings = [
    (0, 60, 10, 9*60, 12*60, 1),   # Monday only
    (1, 90, 20, 9*60, 12*60, 2),   # Tuesday only
    (2, 120, 30, 13*60, 17*60, 4)  # Wednesday only
]

n = len(meetings)
day_names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
best_value = -1
best_day = None
best_schedule = []

for day_index in range(7):
    opt = Optimize()
    start_vars = [Int(f'start_{i}_{day_index}') for i in range(n)]
    include_vars = [Bool(f'include_{i}_{day_index}') for i in range(n)]
    
    # Constraint: Only include meetings available on this day
    for i in range(n):
        mask = 1 << day_index
        if meetings[i][5] & mask:
            pass  # Meeting is available
        else:
            opt.add(include_vars[i] == False)  # Force exclude if not available
    
    # Time window and working hour constraints
    for i in range(n):
        mask = 1 << day_index
        if meetings[i][5] & mask:
            dur, av_start, av_end = meetings[i][1], meetings[i][3], meetings[i][4]
            opt.add(Implies(include_vars[i],
                And(start_vars[i] >= av_start,
                    start_vars[i] + dur <= av_end,
                    start_vars[i] >= 9*60,
                    start_vars[i] + dur <= 17*60)))
    
    # Non-overlapping constraints
    for i in range(n):
        for j in range(i+1, n):
            mask = 1 << day_index
            if (meetings[i][5] & mask) and (meetings[j][5] & mask):
                opt.add(Implies(And(include_vars[i], include_vars[j]),
                    Or(start_vars[i] + meetings[i][1] <= start_vars[j],
                       start_vars[j] + meetings[j][1] <= start_vars[i])))
    
    # Time span constraint
    earliest_start = 24*60
    latest_end = 0
    for i in range(n):
        mask = 1 << day_index
        if meetings[i][5] & mask:
            end_i = start_vars[i] + meetings[i][1]
            earliest_start = If(And(include_vars[i], start_vars[i] < earliest_start), start_vars[i], earliest_start)
            latest_end = If(And(include_vars[i], end_i > latest_end), end_i, latest_end)
    opt.add(latest_end - earliest_start <= 480)
    
    # Total value calculation and maximization
    total_value = Sum([If(include_vars[i], meetings[i][2], 0) for i in range(n)])
    opt.maximize(total_value)
    
    # Solve for current day
    if opt.check() == sat:
        m = opt.model()
        total_val = m.evaluate(total_value)
        total_val_int = total_val.as_long()
        if total_val_int > best_value:
            best_value = total_val_int
            best_day = day_index
            best_schedule = []
            for i in range(n):
                if m.evaluate(include_vars[i]):
                    start_val = m.evaluate(start_vars[i]).as_long()
                    best_schedule.append((i, start_val))

# Output optimal schedule
if best_value == -1:
    print("No valid schedule found")
else:
    print(f"Optimal schedule on {day_names[best_day]}:")
    for (i, start_time) in best_schedule:
        duration = meetings[i][1]
        start_hr, start_min = divmod(start_time, 60)
        end_time = start_time + duration
        end_hr, end_min = divmod(end_time, 60)
        print(f"Meeting {i}: {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    print(f"Total value: {best_value}")