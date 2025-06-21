from z3 import *

def find_meeting_time(participants, meeting_duration):
    # Create a Z3 solver
    s = Solver()

    # Define the day (Monday)
    day = 'Monday'

    # Define the start and end times of the work hours
    start_time = 9 * 60
    end_time = 17 * 60

    # Define the meeting duration
    meeting_duration = meeting_duration * 60

    # Create variables for the start time of the meeting
    start_times = [Int(f'start_time_{p}') for p in participants]

    # Create variables for the end time of the meeting
    end_times = [start_times[i] + meeting_duration for i in range(len(participants))]

    # Add constraints for each participant
    for p in participants:
        # Check if the start or end time of the meeting conflicts with the participant's schedule
        for t in range(start_time, end_time, 30):
            if t < start_times[participants.index(p)] or t >= end_times[participants.index(p)]:
                s.assert_and_track(Or(t < start_times[participants.index(p)], t >= end_times[participants.index(p)]), f'no_conflict_{p}_{t}')

    # Add constraint for the meeting duration
    s.assert_and_track(And([start_times[i] < end_times[i] for i in range(len(participants))]),'meeting_duration')

    # Add constraint for the start time of the meeting
    s.assert_and_track(And([start_times[i] >= start_time for i in range(len(participants))]),'start_time')

    # Add constraint for the end time of the meeting
    s.assert_and_track(And([end_times[i] <= end_time for i in range(len(participants))]), 'end_time')

    # Check if a solution exists
    if s.check() == sat:
        # Get the model
        m = s.model()

        # Extract the start time of the meeting
        start_time = m[start_times[0]].as_long()

        # Calculate the end time of the meeting
        end_time = start_time + meeting_duration

        # Format the start and end times
        start_time = f'{start_time // 60:02d}:{start_time % 60:02d}'
        end_time = f'{end_time // 60:02d}:{end_time % 60:02d}'

        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time}')
        print(f'End Time: {end_time}')
    else:
        print('No solution exists.')

# Define the participants and the meeting duration
participants = ['Gregory', 'Jonathan', 'Barbara', 'Jesse', 'Alan', 'Nicole', 'Catherine']
meeting_duration = 0.5

# Find the meeting time
find_meeting_time(participants, meeting_duration)