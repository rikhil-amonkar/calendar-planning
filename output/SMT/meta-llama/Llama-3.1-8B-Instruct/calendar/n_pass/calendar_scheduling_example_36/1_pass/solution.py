from z3 import *

def schedule_meeting(ryan_schedule, ruth_schedule, denise_schedule, meeting_duration, preferences=None):
    # Define the variables
    day = 'Monday'
    start_time = [9, 0]  # 9:00
    end_time = [17, 0]   # 17:00
    meeting_start = [0] * 2
    meeting_end = [0] * 2

    # Convert the schedules to Z3 time intervals
    ryan_intervals = []
    for i in range(len(ryan_schedule)):
        ryan_intervals.append(Int(f"ryan_{i}")[0] >= ryan_schedule[i][0] * 60 + ryan_schedule[i][1])
        ryan_intervals.append(Int(f"ryan_{i}")[0] <= ryan_schedule[i][1] * 60 + ryan_schedule[i][2])

    ruth_intervals = []
    for i in range(len(ruth_schedule)):
        ruth_intervals.append(Int(f"ruth_{i}")[0] >= ruth_schedule[i][0] * 60 + ruth_schedule[i][1])
        ruth_intervals.append(Int(f"ruth_{i}")[0] <= ruth_schedule[i][1] * 60 + ruth_schedule[i][2])

    denise_intervals = []
    for i in range(len(denise_schedule)):
        denise_intervals.append(Int(f"denise_{i}")[0] >= denise_schedule[i][0] * 60 + denise_schedule[i][1])
        denise_intervals.append(Int(f"denise_{i}")[0] <= denise_schedule[i][1] * 60 + denise_schedule[i][2])

    # Define the meeting time constraints
    meeting_start[0] = Int('meeting_start')[0]
    meeting_end[0] = meeting_start[0] + meeting_duration * 60
    meeting_constraints = [
        meeting_start[0] >= start_time[0] * 60 + start_time[1],
        meeting_start[0] <= end_time[0] * 60 + end_time[1],
        meeting_end[0] >= meeting_start[0],
        meeting_end[0] <= end_time[0] * 60 + end_time[1]
    ]

    # Add constraints for each participant
    for i in range(len(ryan_schedule)):
        meeting_constraints.append(Not(And(meeting_start[0] >= ryan_schedule[i][0] * 60 + ryan_schedule[i][1],
                                          meeting_end[0] <= ryan_schedule[i][1] * 60 + ryan_schedule[i][2])))

    for i in range(len(ruth_schedule)):
        meeting_constraints.append(Not(And(meeting_start[0] >= ruth_schedule[i][0] * 60 + ruth_schedule[i][1],
                                          meeting_end[0] <= ruth_schedule[i][1] * 60 + ruth_schedule[i][2])))

    for i in range(len(denise_schedule)):
        meeting_constraints.append(Not(And(meeting_start[0] >= denise_schedule[i][0] * 60 + denise_schedule[i][1],
                                          meeting_end[0] <= denise_schedule[i][1] * 60 + denise_schedule[i][2])))

    # Add preference constraints
    if preferences is not None:
        for i in range(len(preferences)):
            meeting_constraints.append(Not(And(meeting_start[0] >= preferences[i][0] * 60 + preferences[i][1],
                                               meeting_end[0] <= preferences[i][1] * 60 + preferences[i][2])))

    # Solve the constraints
    s = Solver()
    for c in meeting_constraints:
        s.add(c)

    if s.check() == sat:
        m = s.model()
        start_hour = m[meeting_start[0]].as_long() // 60
        start_minute = m[meeting_start[0]].as_long() % 60
        end_hour = m[meeting_end[0]].as_long() // 60
        end_minute = m[meeting_end[0]].as_long() % 60
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_hour:02d}:{start_minute:02d}\nEnd Time: {end_hour:02d}:{end_minute:02d}"
    else:
        return "No solution found"

# Test the function
ryan_schedule = [[9, 0, 30], [12, 30, 60]]
ruth_schedule = []
denise_schedule = [[9, 30, 60], [12, 0, 60], [14, 30, 60 * 2 + 30]]
meeting_duration = 1
preferences = [[12, 30, 60 * 2 + 30]]  # Denise does not want to meet after 12:30
print(schedule_meeting(ryan_schedule, ruth_schedule, denise_schedule, meeting_duration, preferences))