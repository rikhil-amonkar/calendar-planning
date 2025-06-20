from z3 import *

def schedule_meeting():
    # Define the variables
    day = 'Monday'
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints
    # Denise's schedule
    denise_blocked = [Int('denise_blocked_%d' % i) for i in range(8)]
    for i in range(8):
        if i == 11 or i == 14 or i == 23:
            denise_blocked[i].eq(1)
        else:
            denise_blocked[i].eq(0)
    denise_available = Or([denise_blocked[i] == 0 for i in range(8)])

    # Angela's schedule
    angela_blocked = [Int('angela_blocked_%d' % i) for i in range(8)]
    for i in range(8):
        angela_blocked[i].eq(0)
    angela_available = Or([angela_blocked[i] == 0 for i in range(8)])

    # Natalie's schedule
    natalie_blocked = [Int('natalie_blocked_%d' % i) for i in range(8)]
    for i in range(8):
        if i == 0 or i == 1 or i == 2 or i == 5 or i == 6 or i == 7:
            natalie_blocked[i].eq(1)
        else:
            natalie_blocked[i].eq(0)
    natalie_available = Or([natalie_blocked[i] == 0 for i in range(8)])

    # Meeting duration
    meeting_duration = 30
    start_time_constraints = And(start_time >= 9, start_time <= 17)
    end_time_constraints = And(end_time >= start_time, end_time <= 17)
    duration_constraints = And(end_time - start_time == meeting_duration)

    # Find a solution
    solver = Solver()
    solver.add(start_time_constraints)
    solver.add(end_time_constraints)
    solver.add(duration_constraints)
    solver.add(denise_available.substitute(start_time, start_time / 60).substitute(end_time, end_time / 60))
    solver.add(angela_available.substitute(start_time, start_time / 60).substitute(end_time, end_time / 60))
    solver.add(natalie_available.substitute(start_time, start_time / 60).substitute(end_time, end_time / 60))

    if solver.check() == sat:
        model = solver.model()
        start_hour = model[start_time] // 60
        start_minute = model[start_time] % 60
        end_hour = model[end_time] // 60
        end_minute = model[end_time] % 60
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_hour:02d}:{start_minute:02d}')
        print(f'End Time: {end_hour:02d}:{end_minute:02d}')
    else:
        print('No solution found')

schedule_meeting()