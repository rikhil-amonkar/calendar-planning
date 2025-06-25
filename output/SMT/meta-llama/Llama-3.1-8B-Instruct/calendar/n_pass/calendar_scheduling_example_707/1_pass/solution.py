from z3 import *

def schedule_meeting():
    # Define the variables
    day = [Bool('d1'), Bool('d2'), Bool('d3')]  # Monday, Tuesday, Wednesday
    start_time = [Int('st1'), Int('st2'), Int('st3')]  # Start time in minutes (0-480)
    end_time = [Int('et1'), Int('et2'), Int('et3')]  # End time in minutes (0-480)

    # Define the constraints
    for i in range(3):
        start_time[i] = start_time[i].sort(IntSort())
        end_time[i] = end_time[i].sort(IntSort())
        day[i] = day[i].sort(BoolSort())

    # Ryan's constraints
    ryan_monday = Or([start_time[0] < 930, start_time[0] > 1000, start_time[0] > 1100, start_time[0] > 1300, start_time[0] > 1530])
    ryan_tuesday = Or([start_time[1] < 1130, start_time[1] > 1530])
    ryan_wednesday = Or([start_time[2] < 1200, start_time[2] > 1530, start_time[2] > 1630])
    ryan_constraints = And([ryan_monday, ryan_tuesday, ryan_wednesday])

    # Adam's constraints
    adam_monday = Or([start_time[0] < 900, start_time[0] > 1030, start_time[0] > 1100, start_time[0] > 1330, start_time[0] > 1600, start_time[0] > 1630])
    adam_tuesday = Or([start_time[1] < 900, start_time[1] > 1030, start_time[1] > 1030, start_time[1] > 1530, start_time[1] > 1600])
    adam_wednesday = Or([start_time[2] < 900, start_time[2] > 930, start_time[2] > 1000, start_time[2] > 1130, start_time[2] > 1430, start_time[2] > 1500, start_time[2] > 1600])
    adam_constraints = And([adam_monday, adam_tuesday, adam_wednesday])

    # Meeting duration constraint
    duration_constraint = Implies(And([day[0], start_time[0] >= 930, end_time[0] <= 1730]), end_time[0] - start_time[0] == 30)

    # Adam's preference constraint
    adam_preference = Implies(And([day[0], start_time[0] < 1430]), Or([start_time[0] > 1430, Not(day[0])]))

    # Combine the constraints
    constraints = And([ryan_constraints, adam_constraints, duration_constraint, adam_preference])

    # Add the constraints to the solver
    s = Solver()
    s.add(constraints)

    # Solve the constraints
    s.check()

    # Get the solution
    model = s.model()

    # Extract the solution
    day_index = [i for i, x in enumerate(model[day]) if x == True][0]
    start_time_value = model[start_time[day_index]].as_long() // 60
    end_time_value = model[end_time[day_index]].as_long() // 60

    # Print the solution
    print('SOLUTION:')
    print(f'Day: {["Monday", "Tuesday", "Wednesday"][day_index]}')
    print(f'Start Time: {start_time_value:02d}:00')
    print(f'End Time: {end_time_value:02d}:00')

schedule_meeting()