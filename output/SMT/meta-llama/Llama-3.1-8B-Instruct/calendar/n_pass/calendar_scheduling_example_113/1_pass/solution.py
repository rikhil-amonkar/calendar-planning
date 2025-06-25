from z3 import *

def schedule_meeting(day, start_time, end_time, participants, meeting_duration):
    # Create a Z3 solver
    s = Solver()

    # Define variables for each participant's availability
    participant_vars = {}
    for participant in participants:
        participant_vars[participant] = [Bool(f"{participant}_{i}") for i in range(int((end_time - start_time).total_seconds() / 3600 + 1))]

    # Define the constraints for each participant's availability
    for participant in participants:
        for i, var in enumerate(participant_vars[participant]):
            s.add(var == (start_time + timedelta(hours=i)).time() >= participants[participant].start and
                  var == (start_time + timedelta(hours=i)).time() < participants[participant].end)

    # Define the constraint for the meeting duration
    meeting_start = start_time
    meeting_end = start_time + meeting_duration
    for participant in participants:
        s.add(Or([participant_vars[participant][i] for i in range(int((meeting_end - meeting_start).total_seconds() / 3600 + 1))]))

    # Check if there's a solution
    if s.check() == sat:
        # Get the model
        m = s.model()
        # Find the start time of the meeting
        for i, var in enumerate(participant_vars[participants[0]][0]):
            if m[var]:
                meeting_start = start_time + timedelta(hours=i)
                break
        # Find the end time of the meeting
        for i, var in enumerate(participant_vars[participants[0]][0]):
            if m[participant_vars[participants[0]][i]]:
                meeting_end = start_time + timedelta(hours=i)
                break
        return f"SOLUTION:\nDay: {day}\nStart Time: {meeting_start.strftime('%H:%M')}\nEnd Time: {meeting_end.strftime('%H:%M')}"
    else:
        return "No solution found"

# Define the schedules for each participant
class Schedule:
    def __init__(self, start, end):
        self.start = start
        self.end = end

schedules = {
    "Bradley": [Schedule(time(9, 30), time(10, 0)), Schedule(time(12, 30), time(13, 0)), 
               Schedule(time(13, 30), time(14, 0)), Schedule(time(15, 30), time(16, 0))],
    "Teresa": [Schedule(time(10, 30), time(11, 0)), Schedule(time(12, 0), time(12, 30)), 
               Schedule(time(13, 0), time(13, 30)), Schedule(time(14, 30), time(15, 0))],
    "Elizabeth": [Schedule(time(9, 0), time(9, 30)), Schedule(time(10, 30), time(11, 30)), 
                  Schedule(time(13, 0), time(13, 30)), Schedule(time(14, 30), time(15, 0)), 
                  Schedule(time(15, 30), time(17, 0))],
    "Christian": [Schedule(time(9, 0), time(9, 30)), Schedule(time(10, 30), time(17, 0))]
}

# Define the meeting duration
meeting_duration = timedelta(hours=0.5)

# Find a solution
day = "Monday"
start_time = time(9, 0)
end_time = time(17, 0)
solution = schedule_meeting(day, start_time, end_time, schedules, meeting_duration)
print(solution)