from z3 import *

def find_meeting_time(day, start_time, end_time, schedules):
    # Create a Z3 solver
    solver = Solver()

    # Add constraints for each participant
    for participant, schedule in schedules.items():
        for block in schedule:
            if block[0] < start_time and end_time < block[1]:
                solver.assert(Not(start_time < end_time))
                break

    # Add constraints for meeting duration
    solver.assert(start_time + 0.5 > end_time)

    # Check if there is a solution
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        start_time_value = int(model[start_time].as_real().numerator())
        end_time_value = int(model[end_time].as_real().numerator())

        # Format the solution as a string
        solution = f"SOLUTION:\nDay: {day}\nStart Time: {start_time_value:02d}:{int((model[start_time].as_real().numerator() % 1) * 60):02d}\nEnd Time: {end_time_value:02d}:{int((model[end_time].as_real().numerator() % 1) * 60):02d}"
        return solution
    else:
        return "No solution found"

# Define the existing schedules
schedules = {
    "Gregory": [(9, 30), (11, 30, 12)],
    "Jonathan": [(9, 30), (12, 30, 13), (13, 30, 14), (15, 0, 16), (16, 30, 17)],
    "Barbara": [(10, 30, 11), (13, 30, 14)],
    "Jesse": [(10, 0, 11), (12, 30, 14, 30)],
    "Alan": [(9, 30, 11), (11, 30, 12, 30), (13, 0, 15, 30), (16, 0, 17)],
    "Nicole": [(9, 0, 10, 30), (11, 30, 12), (12, 30, 13, 30), (14, 0, 17)],
    "Catherine": [(9, 0, 10, 30), (12, 0, 13, 30), (15, 0, 15, 30), (16, 0, 16, 30)]
}

# Define the meeting duration
meeting_duration = 0.5

# Define the work hours
work_hours = (9, 17)

# Define the day to meet
day = "Monday"

# Find a time that works for everyone's schedule and constraints
start_time = Int('start_time')
end_time = Int('end_time')
for i in range(work_hours[0]*60, work_hours[1]*60):
    if i % 30 == 0:
        solver = Solver()
        start_time_val = i
        end_time_val = start_time_val + 30
        solver.add(start_time_val >= work_hours[0]*60)
        solver.add(start_time_val < work_hours[1]*60)
        solver.add(end_time_val >= work_hours[0]*60)
        solver.add(end_time_val < work_hours[1]*60)
        for participant, schedule in schedules.items():
            for block in schedule:
                if block[0] < start_time_val and end_time_val < block[1]:
                    solver.assert(Not(start_time_val < end_time_val))
                    break
        solver.assert(start_time_val + 0.5 > end_time_val)
        if solver.check() == sat:
            model = solver.model()
            solution = f"SOLUTION:\nDay: {day}\nStart Time: {int(start_time_val/60):02d}:{int((start_time_val % 60)) if (start_time_val % 60)!= 0 else 0:02d}\nEnd Time: {int(end_time_val/60):02d}:{int((end_time_val % 60)) if (end_time_val % 60)!= 0 else 0:02d}"
            print(solution)
            exit()