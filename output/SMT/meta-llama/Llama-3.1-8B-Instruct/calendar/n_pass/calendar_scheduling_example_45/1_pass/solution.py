from z3 import *

def schedule_meeting(day, start_time, end_time, participants, schedules):
    # Create a Z3 solver
    solver = Solver()

    # Define the time slots for the meeting
    for i in range(len(participants)):
        # Check if the time slot conflicts with any scheduled meetings
        for j in range(len(schedules[participants[i]])):
            if start_time >= schedules[participants[i]][j][0] and start_time < schedules[participants[i]][j][1]:
                solver.add(Not(start_time < end_time))
                break
            elif start_time <= schedules[participants[i]][j][0] and start_time + (end_time - start_time) > schedules[participants[i]][j][0]:
                solver.add(Not(start_time < end_time))
                break
            elif end_time > schedules[participants[i]][j][0] and end_time <= schedules[participants[i]][j][1]:
                solver.add(Not(start_time < end_time))
                break
            elif end_time >= schedules[participants[i]][j][0] and end_time < schedules[participants[i]][j][1]:
                solver.add(Not(start_time < end_time))
                break
            elif start_time < schedules[participants[i]][j][0] and end_time > schedules[participants[i]][j][1]:
                pass
            else:
                solver.add(Not(start_time < end_time))

    # Check if the meeting duration is half an hour
    solver.add(end_time - start_time == 30)

    # Check if the meeting is within the work hours
    solver.add(9 <= start_time)
    solver.add(start_time < 17)
    solver.add(9 <= end_time)
    solver.add(end_time < 17)

    # Check if the meeting is on the specified day
    solver.add(day == "Monday")

    # Solve the constraints
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        return f"SOLUTION:\nDay: Monday\nStart Time: {model[start_time].as_string()}\nEnd Time: {model[end_time].as_string()}"
    else:
        return "No solution found"

# Define the existing schedules
schedules = {
    "Andrew": [],
    "Grace": [],
    "Samuel": [(9, 10.5), (11.5, 12), (13, 13.5), (14, 16), (16.5, 17)]
}

# Define the meeting duration and participants
meeting_duration = 30
participants = ["Andrew", "Grace", "Samuel"]

# Define the day and time slots
day = "Monday"
start_time = Int('start_time')
end_time = Int('end_time')

# Solve the scheduling problem
print(schedule_meeting(day, start_time, end_time, participants, schedules))