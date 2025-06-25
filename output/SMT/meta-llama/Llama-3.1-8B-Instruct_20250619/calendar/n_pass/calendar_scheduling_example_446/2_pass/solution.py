from z3 import *

def schedule_meeting():
    # Define the day of the meeting
    day = "Monday"

    # Define the start and end times of the meeting
    start_time = Int('start_time')
    end_time = start_time + 30

    # Define the constraints for each participant
    megan_busy = Or(start_time >= 9, start_time >= 10, start_time >= 12)
    christine_busy = Or(start_time >= 9, start_time >= 11.5, start_time >= 13, start_time >= 16)
    gabriel_free = True
    sara_busy = Or(start_time >= 11.5, start_time >= 14.5)
    bruce_busy = Or(start_time >= 9.5, start_time >= 10.5, start_time >= 12.5, start_time >= 14.5, start_time >= 16)
    kathryn_busy = Or(start_time >= 10, start_time >= 16)
    billy_busy = Or(start_time >= 9, start_time >= 11, start_time >= 12, start_time >= 14, start_time >= 15.5)

    # Define the constraints for the meeting duration
    meeting_duration = start_time + 30

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(And(9 <= start_time, start_time <= 17))
    solver.add(Not(megan_busy))
    solver.add(Not(christine_busy))
    solver.add(Not(gabriel_free))
    solver.add(Not(sara_busy))
    solver.add(Not(bruce_busy))
    solver.add(Not(kathryn_busy))
    solver.add(Not(billy_busy))
    solver.add(9 <= meeting_duration)
    solver.add(meeting_duration <= 17)

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_time_value:02d}:{(start_time_value % 60):02d}\nEnd Time: {end_time_value:02d}:{(end_time_value % 60):02d}"
    else:
        return "No solution found"

print(schedule_meeting())