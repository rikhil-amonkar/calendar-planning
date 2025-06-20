from z3 import *

def schedule_meeting():
    # Define the variables
    day = 'Monday'
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints
    # Denise's schedule
    denise_blocked = [Int('denise_blocked_%d' % i) for i in range(24)]
    for i in range(24):
        if i == 12 or i == 15:
            denise_blocked[i].declare_kind(BoolSort())
            denise_blocked[i].eq(True)
        else:
            denise_blocked[i].declare_kind(BoolSort())
            denise_blocked[i].eq(False)
    denise_available = Or([denise_blocked[i] == False for i in range(24)])

    # Angela's schedule
    angela_blocked = [Int('angela_blocked_%d' % i) for i in range(24)]
    for i in range(24):
        angela_blocked[i].declare_kind(BoolSort())
        angela_blocked[i].eq(False)
    angela_available = Or([angela_blocked[i] == False for i in range(24)])

    # Natalie's schedule
    natalie_blocked = [Int('natalie_blocked_%d' % i) for i in range(24)]
    for i in range(24):
        if i == 9 or i == 10 or i == 12 or i == 13 or i == 14 or i == 16 or i == 17:
            natalie_blocked[i].declare_kind(BoolSort())
            natalie_blocked[i].eq(True)
        else:
            natalie_blocked[i].declare_kind(BoolSort())
            natalie_blocked[i].eq(False)
    natalie_available = Or([natalie_blocked[i] == False for i in range(24)])

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
    solver.add(denise_available)
    solver.add(angela_available)
    solver.add(natalie_available)

    if solver.check() == sat:
        model = solver.model()
        start_hour = model[start_time].as_long() // 60
        start_minute = model[start_time].as_long() % 60
        end_hour = model[end_time].as_long() // 60
        end_minute = model[end_time].as_long() % 60
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_hour:02d}:{start_minute:02d}')
        print(f'End Time: {end_hour:02d}:{end_minute:02d}')
    else:
        print('No solution found')

schedule_meeting()