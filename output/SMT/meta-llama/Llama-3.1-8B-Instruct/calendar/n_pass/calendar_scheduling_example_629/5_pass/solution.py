from z3 import *

def schedule_meeting(margaret_schedule, alexis_schedule, meeting_duration, day, preference):
    # Create Z3 solver
    s = Solver()

    # Define variables
    day_var = Bool('day')
    start_time_var = Real('start_time')
    end_time_var = Real('end_time')

    # Define constraints
    s.add(Implies(day_var, day == 'Monday'))  # Day of the meeting
    s.add(And(start_time_var >= 9, start_time_var <= 17))  # Start time must be between 9:00 and 17:00
    s.add(end_time_var == start_time_var + meeting_duration)  # End time must be after start time
    s.add(end_time_var <= 17)  # End time must be before 17:00

    # Margaret's constraints
    for margaret_block in margaret_schedule['Monday']:
        s.add(And(start_time_var + meeting_duration > margaret_block[0], start_time_var < margaret_block[1]))  # Start time must be before Margaret's block and end time must be after Margaret's block
    if not preference:
        s.add(start_time_var > 11)  # Start time must be after 11:00 if Margaret doesn't want to meet on Monday

    # Alexis's constraints
    for alexis_block in alexis_schedule['Monday']:
        s.add(And(start_time_var + meeting_duration > alexis_block[0], start_time_var < alexis_block[1]))  # Start time must be before Alexis's block and end time must be after Alexis's block

    # Check if there's a solution
    if s.check() == sat:
        model = s.model()
        start_time_to_meet = model[start_time_var].numerator().as_long() / model[start_time_var].denominator().as_long()
        end_time_to_meet = model[end_time_var].numerator().as_long() / model[end_time_var].denominator().as_long()
        return f'SOLUTION:\nDay: Monday\nStart Time: {int(start_time_to_meet):02d}:{int((start_time_to_meet - int(start_time_to_meet)) * 60):02d}\nEnd Time: {int(end_time_to_meet):02d}:{int((end_time_to_meet - int(end_time_to_meet)) * 60):02d}'
    else:
        return 'No solution found'

# Example usage
margaret_schedule = {
    'Monday': [(10.5, 11), (11.5, 12), (13, 13.5), (15, 17)],
    'Tuesday': [(12, 12.5)]
}
alexis_schedule = {
    'Monday': [(9.5, 11.5), (12.5, 13), (13.5, 17)],
    'Tuesday': [(9, 9.5), (10, 10.5), (13.5, 16.5)]
}
meeting_duration = 0.5  # Half an hour
day = 'Monday'
preference = False

print(schedule_meeting(margaret_schedule, alexis_schedule, meeting_duration, day, preference))