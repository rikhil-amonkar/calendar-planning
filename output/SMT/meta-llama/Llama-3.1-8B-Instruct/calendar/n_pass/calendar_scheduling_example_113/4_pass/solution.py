from z3 import *
from datetime import datetime, timedelta

def schedule_meeting(day, start_hour, end_hour, participants, meeting_duration):
    # Create a Z3 solver
    s = Solver()

    # Define variables for each participant's availability
    participant_vars = {}
    for participant in participants:
        participant_vars[participant] = [Bool(f"{participant}_{i}") for i in range(end_hour - start_hour + 1)]

    # Define the constraints for each participant's availability
    for participant in participants:
        for i, var in enumerate(participant_vars[participant]):
            s.add(var == (start_hour + i) >= participants[participant].start.hour and
                  var == (start_hour + i) < participants[participant].end.hour)

    # Define the constraint for the meeting duration
    for participant in participants:
        s.add(Or([participant_vars[participant][i] for i in range(int((end_hour - start_hour) + 1 - meeting_duration.total_seconds() / 3600))]))

    # Check if there's a solution
    if s.check() == sat:
        # Get the model
        m = s.model()
        # Find the start time of the meeting
        for i, var in enumerate(participant_vars[participants[0]][0]):
            if m[var]:
                meeting_start = start_hour + i
                break
        # Find the end time of the meeting
        for i, var in enumerate(participant_vars[participants[0]][0]):
            if m[participant_vars[participants[0]][i]]:
                meeting_end = start_hour + i
                break
        return f"SOLUTION:\nDay: {day}\nStart Time: {meeting_start:02d}:00\nEnd Time: {meeting_end:02d}:00"
    else:
        return "No solution found"

# Define the schedules for each participant
class Schedule:
    def __init__(self, start, end):
        self.start = datetime.strptime(start, '%H:%M').time()
        self.end = datetime.strptime(end, '%H:%M').time()

schedules = {
    "Bradley": [Schedule('09:30', '10:00'), Schedule('12:30', '13:00'), 
               Schedule('13:30', '14:00'), Schedule('15:30', '16:00')],
    "Teresa": [Schedule('10:30', '11:00'), Schedule('12:00', '12:30'), 
               Schedule('13:00', '13:30'), Schedule('14:30', '15:00')],
    "Elizabeth": [Schedule('09:00', '09:30'), Schedule('10:30', '11:30'), 
                  Schedule('13:00', '13:30'), Schedule('14:30', '15:00'), 
                  Schedule('15:30', '17:00')],
    "Christian": [Schedule('09:00', '09:30'), Schedule('10:30', '17:00')]
}

# Define the meeting duration
meeting_duration = timedelta(hours=0.5)

# Find a solution
day = "Monday"
start_hour = 9
end_hour = 17
solution = schedule_meeting(day, start_hour, end_hour, schedules, meeting_duration)
print(solution)