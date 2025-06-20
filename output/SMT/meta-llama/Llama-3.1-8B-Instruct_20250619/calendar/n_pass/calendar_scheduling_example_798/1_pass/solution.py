from z3 import *

def schedule_meeting(nancy_schedule, jose_schedule, meeting_duration):
    # Create Z3 variables
    days = [Int(f'day') for _ in range(3)]
    start_times = [Int(f'start_time') for _ in range(3)]
    end_times = [Int(f'end_time') for _ in range(3)]

    # Create Z3 constraints
    for i in range(3):
        days[i].sort(IntSort())
        days[i].declare_kind(IntSort())
        days[i].get_sort().assert_and_track(days[i] >= 0, "days_positive")
        days[i].get_sort().assert_and_track(days[i] <= 2, "days_in_range")

    for i in range(3):
        start_times[i].sort(IntSort())
        start_times[i].declare_kind(IntSort())
        start_times[i].get_sort().assert_and_track(start_times[i] >= 0, "start_time_positive")
        start_times[i].get_sort().assert_and_track(start_times[i] <= 16, "start_time_in_range")

    for i in range(3):
        end_times[i].sort(IntSort())
        end_times[i].declare_kind(IntSort())
        end_times[i].get_sort().assert_and_track(end_times[i] >= 0, "end_time_positive")
        end_times[i].get_sort().assert_and_track(end_times[i] <= 16, "end_time_in_range")

    # Constraints for meeting duration
    for i in range(3):
        end_times[i] = start_times[i] + meeting_duration

    # Constraints for nancy's schedule
    for day in range(3):
        for start, end in nancy_schedule[day]:
            constraints = [start_times[day] > start, end_times[day] < end]
            if day == 0:
                constraints.append(days[day] == 0)
            elif day == 1:
                constraints.append(days[day] == 1)
            else:
                constraints.append(days[day] == 2)
            solver = Solver()
            solver.add(And(constraints))
            if not solver.check():
                continue
            model = solver.model()
            start_time = model[start_times[day]].as_long()
            end_time = model[end_times[day]].as_long()
            if start_time == end_time:
                continue
            print(f"Nancy is busy on day {day} from {start}:{start_time % 60:02d} to {end}:{end_time % 60:02d}")
            return None

    # Constraints for jose's schedule
    for day in range(3):
        for start, end in jose_schedule[day]:
            constraints = [start_times[day] > start, end_times[day] < end]
            if day == 0:
                constraints.append(days[day] == 0)
            elif day == 1:
                constraints.append(days[day] == 1)
            else:
                constraints.append(days[day] == 2)
            solver = Solver()
            solver.add(And(constraints))
            if not solver.check():
                continue
            model = solver.model()
            start_time = model[start_times[day]].as_long()
            end_time = model[end_times[day]].as_long()
            if start_time == end_time:
                continue
            print(f"Jose is busy on day {day} from {start}:{start_time % 60:02d} to {end}:{end_time % 60:02d}")
            return None

    # Solve the system of constraints
    solver = Solver()
    solver.add(And([days[0]!= 1, days[0]!= 2, days[1]!= 0, days[1]!= 2, days[2]!= 0, days[2]!= 1]))
    solver.add(And([start_times[0] >= 9, start_times[0] <= 16, start_times[1] >= 9, start_times[1] <= 16, start_times[2] >= 9, start_times[2] <= 16]))
    solver.add(And([end_times[0] >= 9, end_times[0] <= 16, end_times[1] >= 9, end_times[1] <= 16, end_times[2] >= 9, end_times[2] <= 16]))
    solver.add(And([days[0] == 0, start_times[0] >= 9, start_times[0] <= 16, end_times[0] >= 9, end_times[0] <= 16]))
    solver.add(And([days[1] == 1, start_times[1] >= 9, start_times[1] <= 16, end_times[1] >= 9, end_times[1] <= 16]))
    solver.add(And([days[2] == 2, start_times[2] >= 9, start_times[2] <= 16, end_times[2] >= 9, end_times[2] <= 16]))

    # Add constraints for meeting duration
    for i in range(3):
        solver.add(end_times[i] == start_times[i] + 30)

    # Add constraints for nancy's schedule
    for day in range(3):
        for start, end in nancy_schedule[day]:
            constraints = [start_times[day] > start, end_times[day] < end]
            if day == 0:
                constraints.append(days[day] == 0)
            elif day == 1:
                constraints.append(days[day] == 1)
            else:
                constraints.append(days[day] == 2)
            solver.add(Or([Not(constraint) for constraint in constraints]))

    # Add constraints for jose's schedule
    for day in range(3):
        for start, end in jose_schedule[day]:
            constraints = [start_times[day] > start, end_times[day] < end]
            if day == 0:
                constraints.append(days[day] == 0)
            elif day == 1:
                constraints.append(days[day] == 1)
            else:
                constraints.append(days[day] == 2)
            solver.add(Or([Not(constraint) for constraint in constraints]))

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        day = model[days[0]].as_long()
        start_time = model[start_times[0]].as_long()
        end_time = model[end_times[0]].as_long()
        return f"SOLUTION:\nDay: {['Monday', 'Tuesday', 'Wednesday'][day]}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00"
    else:
        return "No solution exists"

# Define nancy's schedule
nancy_schedule = [[[10, 10], [11, 11], [13, 14], [14, 15], [16, 17]],
                  [[9, 10], [11, 11], [12, 12], [13, 13], [15, 16]],
                  [[10, 11], [13, 16]]]

# Define jose's schedule
jose_schedule = [[[9, 17]],
                  [[9, 17]],
                  [[9, 9], [10, 12], [13, 14], [15, 17]]]

# Define meeting duration
meeting_duration = 30

print(schedule_meeting(nancy_schedule, jose_schedule, meeting_duration))