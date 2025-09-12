from z3 import *

# Define the days and their occupied i lists
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
occupied = {
    "Monday": [0, 3, 7, 11, 12, 15],
    "Tuesday": [0,1,2,3,5,7,8,9,10,11,12,14,15],
    "Wednesday": [2,3,6,7,9,10,11,12,13],
    "Thursday": [1,2,3,4,5,6,8,10,15]
}

for day in days:
    solver = Solver()
    i = Int('i')
    solver.add(And(i >= 0, i <= 15))
    if occupied[day]:
        solver.add(Not(Or([i == o for o in occupied[day]])))
    if solver.check() == sat:
        model = solver.model()
        selected_i = model[i].as_long()
        start_minutes = selected_i * 30
        start_hour = 9 + start_minutes // 60
        start_min = start_minutes % 60
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        start_time = f"{start_hour:02d}:{start_min:02d}"
        end_time = f"{end_hour:02d}:{end_min:02d}"
        print(f"{day} {start_time}:{end_time}")
        break