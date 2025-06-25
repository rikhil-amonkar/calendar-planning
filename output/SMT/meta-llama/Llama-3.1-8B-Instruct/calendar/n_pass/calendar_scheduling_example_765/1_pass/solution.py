from z3 import *

def schedule_meeting(joshua_schedule, joyce_schedule, preferred_days, meeting_duration):
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Create a Z3 solver
    solver = Solver()
    
    # Define the variables
    day = [Bool(f'day_{i}') for i in range(len(days))]
    start_time = [Int(f'start_time_{i}') for i in range(len(days))]
    end_time = [Int(f'end_time_{i}') for i in range(len(days))]
    
    # Add constraints for the day
    for i, d in enumerate(day):
        solver.add(Or([d]))
        solver.add(Implies(d, start_time[i] >= 9 * 60))
        solver.add(Implies(d, start_time[i] <= 17 * 60))
        solver.add(Implies(d, end_time[i] >= 9 * 60))
        solver.add(Implies(d, end_time[i] <= 17 * 60))
        solver.add(Implies(d, start_time[i] < end_time[i]))
    
    # Add constraints for the meeting duration
    for i in range(len(days)):
        solver.add(Implies(day[i], end_time[i] - start_time[i] == meeting_duration * 60))
    
    # Add constraints for the schedules
    for i in range(len(days)):
        for joshua_time in joshua_schedule.get(days[i], []):
            solver.add(Not(And(day[i], start_time[i] >= joshua_time[0], start_time[i] < joshua_time[1])))
        for joyce_time in joyce_schedule.get(days[i], []):
            solver.add(Not(And(day[i], start_time[i] >= joyce_time[0], start_time[i] < joyce_time[1])))
    
    # Add constraints for the preferred days
    for day_name in preferred_days:
        if day_name in days:
            solver.add(day[days.index(day_name)])
        else:
            solver.add(Not(Or([day[days.index(d)] for d in days if d == day_name])))
    
    # Add constraints for Joyce's preference
    solver.add(Implies(And(day[1], start_time[1] < 12 * 60), Not(And(day[1], start_time[1] < 12 * 60, start_time[1] >= 9 * 60))))
    
    # Check if there is a solution
    if solver.check() == sat:
        # Get the model
        model = solver.model()
        
        # Print the solution
        day_name = days[model.evaluate(day[0]).as_bool()]
        start_time_value = model.evaluate(start_time[0]).as_long() // 60
        end_time_value = model.evaluate(end_time[0]).as_long() // 60
        print(f'SOLUTION:')
        print(f'Day: {day_name}')
        print(f'Start Time: {start_time_value:02d}:{(start_time_value % 60):02d}')
        print(f'End Time: {end_time_value:02d}:{(end_time_value % 60):02d}')
    else:
        print('No solution found.')

# Define the schedules
joshua_schedule = {
    'Monday': [(15 * 60, 15 * 60 + 30)],
    'Tuesday': [(11 * 60, 12 * 60), (13 * 60, 13 * 60 + 30), (14 * 60, 15 * 60)]
}

joyce_schedule = {
    'Monday': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (11 * 60, 12 * 60), (13 * 60, 15 * 60), (15 * 60, 17 * 60)],
    'Tuesday': [(9 * 60, 17 * 60)],
    'Wednesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (12 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)]
}

# Define the preferred days
preferred_days = ['Monday', 'Tuesday', 'Wednesday']

# Define the meeting duration
meeting_duration = 0.5

# Schedule the meeting
schedule_meeting(joshua_schedule, joyce_schedule, preferred_days, meeting_duration)