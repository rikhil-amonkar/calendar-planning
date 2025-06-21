from z3 import *

def schedule_meeting(day, meeting_duration, constraints):
    """
    Schedule a meeting for the given participants on the given day.

    Parameters:
    day (str): The day of the week.
    meeting_duration (int): The duration of the meeting in minutes.
    constraints (dict): A dictionary where the keys are the participant names and the values are lists of time intervals they are busy.

    Returns:
    str: A string describing the scheduled meeting time.
    """

    # Create a Z3 solver
    s = Solver()

    # Define the time intervals for the day
    intervals = []
    for hour in range(9, 17):
        for minute in range(0, 60, 30):
            start_time = hour * 60 + minute
            end_time = start_time + 30
            intervals.append((start_time, end_time))

    # Define the variables for the meeting time
    meeting_start = [Int(f'meeting_start_{i}') for i in range(len(intervals))]
    meeting_end = [Int(f'meeting_end_{i}') for i in range(len(intervals))]

    # Define the constraints for each participant
    for i, interval in enumerate(intervals):
        for participant, busy_intervals in constraints.items():
            for busy_interval in busy_intervals:
                if busy_interval[0] <= interval[0] < busy_interval[1]:
                    s.add(meeting_start[i] >= busy_interval[1])
                elif busy_interval[0] < interval[1] <= busy_interval[1]:
                    s.add(meeting_start[i] <= busy_interval[0])
                elif interval[0] < busy_interval[0] < interval[1]:
                    s.add(meeting_end[i] >= busy_interval[0])

    # Define the constraints for the meeting duration
    for i in range(len(intervals)):
        s.add(meeting_end[i] - meeting_start[i] == meeting_duration)

    # Add the constraint that the meeting should not start before 10:00 for Megan
    for i in range(len(intervals)):
        if intervals[i][0] >= 9 * 60 + 30:
            s.add(meeting_start[i] >= intervals[i][0])

    # Add the constraint that the meeting should not conflict with existing meetings
    for i in range(len(intervals)):
        for j in range(i + 1, len(intervals)):
            s.add(meeting_start[i] + meeting_duration <= meeting_start[j] or meeting_start[j] + meeting_duration <= meeting_start[i])

    # Solve the constraints
    if s.check() == sat:
        # Get the solution
        model = s.model()
        for i in range(len(intervals)):
            if model[meeting_start[i]]!= 0:
                start_time = model[meeting_start[i]].as_long()
                end_time = model[meeting_end[i]].as_long()
                return f'SOLUTION:\nDay: {day}\nStart Time: {start_time // 60:02d}:{start_time % 60:02d}\nEnd Time: {end_time // 60:02d}:{end_time % 60:02d}'
    return 'No solution found'

# Example usage
day = 'Monday'
meeting_duration = 30
constraints = {
    'Kimberly': [(10 * 60 + 0, 10 * 60 + 30), (11 * 60 + 0, 12 * 60 + 0), (16 * 60 + 0, 16 * 60 + 30)],
    'Megan': [],
    'Marie': [(10 * 60 + 0, 11 * 60 + 0), (11 * 60 + 30, 15 * 60 + 0), (16 * 60 + 0, 16 * 60 + 30)],
    'Diana': [(9 * 60 + 30, 10 * 60 + 0), (10 * 60 + 30, 14 * 60 + 30), (15 * 60 + 30, 17 * 60 + 0)]
}
print(schedule_meeting(day, meeting_duration, constraints))