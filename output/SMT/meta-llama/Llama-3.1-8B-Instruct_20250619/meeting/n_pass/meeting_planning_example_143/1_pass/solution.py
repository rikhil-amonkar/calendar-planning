from z3 import *

# Define the variables
start_time = 0  # Start time in minutes after 9:00AM
end_time = 12 * 60  # End time in minutes after 9:00AM

# Define the constraints
s = Optimize()

# Define the variables for meeting times
karen_meeting_time = Int('karen_meeting_time')
mark_meeting_time = Int('mark_meeting_time')

# Define the constraints for meeting times
s.add(karen_meeting_time >= 9 * 60 + 45)  # Karen is available from 6:45PM
s.add(karen_meeting_time <= 20 * 60 + 15)  # Karen is available until 8:15PM
s.add(mark_meeting_time >= 13 * 60)  # Mark is available from 1:00PM
s.add(mark_meeting_time <= 17 * 60 + 45)  # Mark is available until 5:45PM
s.add(karen_meeting_time >= 9 * 60 + 45 - 90)  # Karen is available for at least 90 minutes
s.add(karen_meeting_time <= 20 * 60 + 15 + 90)  # Karen is available for at least 90 minutes
s.add(mark_meeting_time >= 13 * 60 - 120)  # Mark is available for at least 120 minutes
s.add(mark_meeting_time <= 17 * 60 + 45 + 120)  # Mark is available for at least 120 minutes

# Define the objective function
s.add(karen_meeting_time + mark_meeting_time)

# Solve the optimization problem
s.maximize(karen_meeting_time + mark_meeting_time)

# Solve the problem
solution = s.check()

# If there is a solution, print it
if solution == sat:
    model = s.model()
    print("Best meeting time for Karen:", model[karen_meeting_time])
    print("Best meeting time for Mark:", model[mark_meeting_time])
    # Calculate the schedule
    schedule = []
    if model[karen_meeting_time] >= 9 * 60 + 45 and model[karen_meeting_time] <= 20 * 60 + 15:
        schedule.append("Meet Karen at Pacific Heights from " + str((model[karen_meeting_time] - 90) // 60) + ":" + str((model[karen_meeting_time] - 90) % 60).zfill(2) + " to " + str(model[karen_meeting_time] // 60) + ":" + str(model[karen_meeting_time] % 60).zfill(2))
    if model[mark_meeting_time] >= 13 * 60 and model[mark_meeting_time] <= 17 * 60 + 45:
        schedule.append("Meet Mark at Embarcadero from " + str((model[mark_meeting_time] - 120) // 60) + ":" + str((model[mark_meeting_time] - 120) % 60).zfill(2) + " to " + str(model[mark_meeting_time] // 60) + ":" + str(model[mark_meeting_time] % 60).zfill(2))
    schedule.sort(key=lambda x: int(x.split(" ")[-1].split(":")[0]))
    schedule.sort(key=lambda x: int(x.split(" ")[-1].split(":")[1]))
    print("Optimal schedule:")
    for i in range(len(schedule)):
        print(str(i+1) + ". " + schedule[i])
else:
    print("No solution found")