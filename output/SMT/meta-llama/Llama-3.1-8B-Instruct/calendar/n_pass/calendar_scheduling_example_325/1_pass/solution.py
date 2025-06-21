from z3 import *

# Define the day
day = 'Monday'

# Define the start and end times
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the existing schedules
schedules = {
    'Jose': [(11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60)],
    'Keith': [(14 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30)],
    'Logan': [(9 * 60, 10 * 60), (12 * 60, 12 * 60 + 30), (15 * 60, 15 * 60 + 30)],
    'Megan': [(9 * 60, 10 * 60 + 30), (11 * 60, 12 * 60), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 16 * 60 + 30)],
    'Gary': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 16 * 60 + 30)],
    'Bobby': [(11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 16 * 60)]
}

# Define Jose's preference
jose_preference = lambda x: x < 15 * 60

# Create a Z3 solver
solver = Solver()

# Define the meeting time
meeting_time = Int('meeting_time')

# Add constraints for each person
for person in schedules:
    for start, end in schedules[person]:
        if start <= meeting_time + meeting_duration <= end:
            solver.assert_and_track(meeting_time + meeting_duration > end, f'{person}_1')
            solver.assert_and_track(meeting_time < start, f'{person}_2')

# Add constraint for Jose's preference
solver.assert_and_track(jose_preference(meeting_time), 'jose_preference')

# Add constraints for the day and meeting duration
solver.assert_and_track(meeting_time >= start_time,'start_time')
solver.assert_and_track(meeting_time + meeting_duration <= end_time, 'end_time')

# Check the solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[meeting_time].as_long()
    end_time = start_time + meeting_duration
    print(f'SOLUTION:\nDay: {day}\nStart Time: {start_time // 60:02d}:{start_time % 60:02d}\nEnd Time: {end_time // 60:02d}:{end_time % 60:02d}')
else:
    print('No solution found')