from z3 import *

def schedule_meeting(judith_schedule, timothy_schedule, meeting_duration, day_preferences, judith_preferences):
    # Create Z3 variables
    days = [Int(f'day') for _ in range(3)]
    for i, day in enumerate(days):
        day.eq(1 + i)  # Assign day value (Monday=1, Tuesday=2, Wednesday=3)
    
    judith_start_times = [Int(f'judith_start_{i}') for i in range(8)]
    judith_end_times = [Int(f'judith_end_{i}') for i in range(8)]
    for i in range(8):
        judith_start_times[i].eq(9 + i)
        judith_end_times[i].eq(judith_start_times[i] + meeting_duration)
    
    timothy_start_times = [Int(f'timothy_start_{i}') for i in range(14)]
    timothy_end_times = [Int(f'timothy_end_{i}') for i in range(14)]
    for i in range(14):
        timothy_start_times[i].eq(9 + i)
        timothy_end_times[i].eq(timothy_start_times[i] + meeting_duration)
    
    # Define constraints
    constraints = []
    
    # Judith's constraints
    for i, (start, end) in enumerate(judith_schedule):
        constraints.append(And(start <= judith_start_times[i], judith_end_times[i] <= end))
    
    for i, (start, end) in enumerate(judith_preferences):
        if judith_preferences[i][0] == 'Monday' and judith_preferences[i][1] == 'before 12:00':
            constraints.append(And(judith_start_times[i] > 11, days[0] == 1))
        elif judith_preferences[i][0] == 'Wednesday' and judith_preferences[i][1] == 'before 12:00':
            constraints.append(And(judith_start_times[i] > 11, days[2] == 1))
    
    # Timothy's constraints
    for i, (start, end) in enumerate(timothy_schedule):
        constraints.append(And(start <= timothy_start_times[i], timothy_end_times[i] <= end))
    
    # Meeting duration constraint
    constraints.append(And(meeting_duration <= 1))
    
    # Day preference constraint
    constraints.append(Or([days[0] == day_value for day_value in day_preferences]))
    
    # Solve the problem
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        day = model[days[0]]
        judith_start = model[judith_start_times[0]]
        judith_end = model[judith_end_times[0]]
        return f'SOLUTION:\nDay: {["Monday", "Tuesday", "Wednesday"][day.as_long() - 1]}\nStart Time: {judith_start.as_long():02d}:00\nEnd Time: {judith_end.as_long():02d}:00'
    else:
        return 'No solution found'

# Example usage
judith_schedule = [(12, 12.5), (11.5, 12)]
timothy_schedule = [(9.5, 10), (10.5, 11.5), (12.5, 14.5), (15.5, 17.5), 
                    (9.5, 13), (13.5, 14), (14.5, 17.5), 
                    (9, 9.5), (10.5, 11), (13.5, 14.5), (15, 15.5), (16, 16.5)]
meeting_duration = 1
day_preferences = [1, 2, 3]
judith_preferences = [['Monday', 'avoid'], ['Wednesday', 'before 12:00']]

print(schedule_meeting(judith_schedule, timothy_schedule, meeting_duration, day_preferences, judith_preferences))