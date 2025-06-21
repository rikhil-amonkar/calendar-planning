from z3 import *

def schedule_meeting(participants, start_time, end_time, meeting_duration):
    # Create a Z3 solver
    s = Solver()

    # Define the variables
    times = [Int(f'time_{i}') for i in range(len(participants))]
    for i in range(len(participants)):
        s.add(ForAll([i], And(times[i] >= start_time, times[i] <= end_time)))

    # Add constraints for each participant
    for i, participant in enumerate(participants):
        for time in participant:
            s.add(Or(times[i] < time[0], times[i] > time[1]))

    # Add constraint for meeting duration
    s.add(And(times[0] + meeting_duration <= end_time, 
              times[0] + meeting_duration >= start_time))

    # Add constraint to ensure all participants are present
    s.add(And([times[i] >= times[0] for i in range(1, len(participants))]))
    s.add(And([times[i] >= times[0] + meeting_duration for i in range(1, len(participants))]))

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        start_time = model[times[0]].as_long()
        return f'SOLUTION:\nDay: Monday\nStart Time: {start_time:02d}:00\nEnd Time: {(start_time + meeting_duration):02d}:00'
    else:
        return 'No solution found'

# Define the existing schedules for each participant
olivia = [(12*60 + 30, 13*60 + 30), (14*60 + 30, 15*60 + 0), (16*60 + 30, 17*60 + 0)]
anna = []
virginia = [(9*60, 10*60), (11*60 + 30, 16*60), (16*60 + 30, 17*60 + 0)]
paul = [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (13*60, 14*60), (14*60 + 30, 16*60), (16*60 + 30, 17*60 + 0)]

# Define the meeting duration and start time
meeting_duration = 60  # 1 hour
start_time = 9 * 60  # 9:00

# Solve the problem
print(schedule_meeting([olivia, anna, virginia, paul], start_time, 17 * 60, meeting_duration))