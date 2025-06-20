from z3 import *

def schedule_meeting(juan_schedule, marilyn_schedule, ronald_schedule, meeting_duration, max_end_time):
    # Create Z3 variables for the meeting time
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Ensure the meeting starts and ends within the work hours
    start_time_ge = start_time >= 9
    start_time_le = start_time <= max_end_time
    end_time_ge = end_time >= start_time
    end_time_le = end_time <= max_end_time

    # Ensure the meeting duration is correct
    duration = end_time - start_time
    duration_eq = duration == meeting_duration

    # Ensure the meeting time does not conflict with Juan's schedule
    for j_start, j_end in juan_schedule:
        conflict_juan = start_time >= j_start
        conflict_juan &= start_time + meeting_duration <= j_end
        conflict_juan |= start_time + meeting_duration >= j_start
        conflict_juan &= start_time < j_end
        conflict_juan |= end_time > j_start
        conflict_juan &= start_time + meeting_duration <= max_end_time
        conflict_juan &= end_time >= start_time
        conflict_juan &= end_time <= max_end_time
        start_time, end_time = start_time.dist('start_time', 1), end_time.dist('end_time', 1)
        conflict_juan = Or(conflict_juan)
        start_time, end_time = start_time.dist('start_time', -1), end_time.dist('end_time', -1)

    # Ensure the meeting time does not conflict with Marilyn's schedule
    for m_start, m_end in marilyn_schedule:
        conflict_marilyn = start_time >= m_start
        conflict_marilyn &= start_time + meeting_duration <= m_end
        conflict_marilyn |= start_time + meeting_duration >= m_start
        conflict_marilyn &= start_time < m_end
        conflict_marilyn |= end_time > m_start
        conflict_marilyn &= start_time + meeting_duration <= max_end_time
        conflict_marilyn &= end_time >= start_time
        conflict_marilyn &= end_time <= max_end_time
        start_time, end_time = start_time.dist('start_time', 1), end_time.dist('end_time', 1)
        conflict_marilyn = Or(conflict_marilyn)
        start_time, end_time = start_time.dist('start_time', -1), end_time.dist('end_time', -1)

    # Ensure the meeting time does not conflict with Ronald's schedule
    for r_start, r_end in ronald_schedule:
        conflict_ronald = start_time >= r_start
        conflict_ronald &= start_time + meeting_duration <= r_end
        conflict_ronald |= start_time + meeting_duration >= r_start
        conflict_ronald &= start_time < r_end
        conflict_ronald |= end_time > r_start
        conflict_ronald &= start_time + meeting_duration <= max_end_time
        conflict_ronald &= end_time >= start_time
        conflict_ronald &= end_time <= max_end_time
        start_time, end_time = start_time.dist('start_time', 1), end_time.dist('end_time', 1)
        conflict_ronald = Or(conflict_ronald)
        start_time, end_time = start_time.dist('start_time', -1), end_time.dist('end_time', -1)

    # Ensure Juan can not meet after 16:00
    conflict_juan_end = start_time + meeting_duration > 16

    # Solve the Z3 constraints
    solver = Solver()
    solver.add([start_time_ge, start_time_le, end_time_ge, end_time_le, duration_eq, 
                Not(conflict_juan), Not(conflict_marilyn), Not(conflict_ronald), 
                Not(conflict_juan_end)])
    if solver.check() == sat:
        model = solver.model()
        day = 'Monday'
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value:02d}:{(start_time_value % 60):02d}\nEnd Time: {end_time_value:02d}:{(end_time_value % 60):02d}'
    else:
        return 'No solution found'

# Define the existing schedules
juan_schedule = [(9, 10.5), (15.5, 16)]
marilyn_schedule = [(11, 11.5), (12.5, 13)]
ronald_schedule = [(9, 10.5), (12, 12.5), (13, 13.5), (14, 16.5)]

# Define the meeting duration and maximum end time
meeting_duration = 0.5
max_end_time = 17

print(schedule_meeting(juan_schedule, marilyn_schedule, ronald_schedule, meeting_duration, max_end_time))