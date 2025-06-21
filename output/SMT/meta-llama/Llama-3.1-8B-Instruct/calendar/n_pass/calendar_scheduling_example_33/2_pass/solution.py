from z3 import *

def schedule_meeting(lisa_schedule, bobby_schedule, randy_schedule, meeting_duration, bobby_preference):
    # Create a Z3 solver
    s = Solver()

    # Define the day and time variables
    days = ['Monday']
    times = [str(i) + ':00' for i in range(9, 17)] + [str(i) + ':30' for i in range(9, 17)]
    times = [t +'to'+ t2 if i < len(times) - 1 else t for i, (t, t2) in enumerate(zip(times, times[1:] + [times[-1] +'to 17:00']))]

    # Define the meeting time variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints for each participant's schedule
    for i, (schedule, name) in enumerate(zip([lisa_schedule, bobby_schedule, randy_schedule], ['Lisa', 'Bobby', 'Randy'])):
        for time in schedule:
            start, end = time.split(' to ')
            start = int(start[:-3]) * 60 + int(start[-2:])
            end = int(end[:-3]) * 60 + int(end[-2:])
            s.add(Or(And(start_time >= start, end_time <= end), 
                     And(start_time >= end, end_time <= start)))

    # Define the constraints for the meeting duration
    s.add(And(start_time + 30 <= end_time, start_time >= 0, end_time <= 17 * 60))

    # Define the constraint for Bobby's preference
    if bobby_preference:
        s.add(And(start_time >= 0, end_time <= 15 * 60))

    # Define the constraints for the day
    s.add(day == 0)  # Monday is 0

    # Define the objective function
    s.add(Implies(day == 0, And(start_time >= 9 * 60, start_time <= 16 * 60)))

    # Define the objective function
    s.add(Or(And(start_time >= 9 * 60, start_time < 9 * 60 + 30), 
             And(start_time >= 9 * 60 + 30, start_time < 10 * 60), 
             And(start_time >= 10 * 60, start_time < 10 * 60 + 30), 
             And(start_time >= 10 * 60 + 30, start_time < 11 * 60), 
             And(start_time >= 11 * 60, start_time < 11 * 60 + 30), 
             And(start_time >= 11 * 60 + 30, start_time < 12 * 60), 
             And(start_time >= 12 * 60, start_time < 12 * 60 + 30), 
             And(start_time >= 12 * 60 + 30, start_time < 13 * 60), 
             And(start_time >= 13 * 60, start_time < 13 * 60 + 30), 
             And(start_time >= 13 * 60 + 30, start_time < 14 * 60), 
             And(start_time >= 14 * 60, start_time < 14 * 60 + 30), 
             And(start_time >= 14 * 60 + 30, start_time < 15 * 60), 
             And(start_time >= 15 * 60, start_time < 15 * 60 + 30), 
             And(start_time >= 15 * 60 + 30, start_time < 16 * 60), 
             And(start_time >= 16 * 60, start_time < 16 * 60 + 30)))

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        day = days[model[day].as_long()]
        start_time = str(model[start_time].as_long() // 60) + ':' + str(model[start_time].as_long() % 60).zfill(2)
        end_time = str(model[end_time].as_long() // 60) + ':' + str(model[end_time].as_long() % 60).zfill(2)
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time}\nEnd Time: {end_time}'
    else:
        return 'No solution found'

# Example usage
lisa_schedule = ['09:00 to 10:00', '10:30 to 11:30', '12:30 to 13:00', '16:00 to 16:30']
bobby_schedule = ['09:00 to 09:30', '10:00 to 10:30', '11:30 to 12:00', '15:00 to 15:30']
randy_schedule = ['09:30 to 10:00', '10:30 to 11:00', '11:30 to 12:30', '13:00 to 13:30', '14:30 to 15:30', '16:00 to 16:30']
meeting_duration = 30
bobby_preference = True

print(schedule_meeting(lisa_schedule, bobby_schedule, randy_schedule, meeting_duration, bobby_preference))