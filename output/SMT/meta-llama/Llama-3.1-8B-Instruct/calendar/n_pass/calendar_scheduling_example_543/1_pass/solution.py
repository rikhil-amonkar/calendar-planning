from z3 import *

def schedule_meeting(schedules, meeting_duration):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    days = ['Monday']
    start_times = [str(i) + ':00' for i in range(9, 18)]  # 9:00 to 17:00
    end_times = [str(int(st.split(':')[0]) + meeting_duration) + ':00' for st in start_times]

    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Add constraints for the day
    solver.add(day == 0)  # Only Monday for now
    solver.add(And(day >= 0, day < len(days)))

    # Add constraints for the start time
    solver.add(And(start_time >= 0, start_time < len(start_times)))
    solver.add(And(end_time >= 0, end_time < len(end_times)))

    # Add constraints for the meeting duration
    solver.add(start_time < end_time)

    # Add constraints for the schedules
    for i, schedule in enumerate(schedules):
        day_var = If(i == 0, day, day == 0)
        start_time_var = If(i == 0, start_time, start_time == 0)
        end_time_var = If(i == 0, end_time, end_time == 0)
        solver.add(Or(
            start_time_var + meeting_duration > schedule[1] + 1,  # End time is after the schedule
            start_time_var < schedule[0],  # Start time is before the schedule
            end_time_var < schedule[0],  # End time is before the schedule
            end_time_var > schedule[1] + 1  # Start time is after the schedule
        ))

    # Check if there is a solution
    if solver.check() == sat:
        model = solver.model()
        day_value = days[model[day].as_long()]
        start_time_value = start_times[model[start_time].as_long()]
        end_time_value = end_times[model[end_time].as_long()]
        return f"SOLUTION:\nDay: {day_value}\nStart Time: {start_time_value}\nEnd Time: {end_time_value}"
    else:
        return "No solution found"

# Example usage
schedules = [[11*60, 12*60], [9*60, 11*60], [11*60, 12*60], [12*30*60, 13*30*60], [14*30*60, 16*30*60]]
meeting_duration = 60
print(schedule_meeting(schedules, meeting_duration))