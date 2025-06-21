from z3 import *

def find_meeting_time():
    # Define the variables
    day = "Monday"
    start_time = Int('start_time')
    end_time = start_time + 30  # Meeting duration is 30 minutes
    participants = [
        "Patrick", "Shirley", "Jeffrey", "Gloria", "Nathan", "Angela", "David"
    ]

    # Define the constraints
    constraints = [
        And(start_time >= 9 * 60, start_time < 17 * 60),  # Work hours
        start_time + 30 < 17 * 60,
        Or(
            start_time == 9 * 60 + 30,
            start_time == 10 * 60 + 30,
            start_time == 11 * 60 + 30,
            start_time == 12 * 60 + 30,
            start_time == 13 * 60 + 30,
            start_time == 14 * 60 + 30,
            start_time == 15 * 60 + 30,
            start_time == 16 * 60 + 30
        ),
        Or(
            start_time == 9 * 60,
            start_time == 10 * 60,
            start_time == 11 * 60,
            start_time == 12 * 60,
            start_time == 13 * 60,
            start_time == 14 * 60,
            start_time == 15 * 60,
            start_time == 16 * 60
        )
    ]

    # Define participant constraints
    patrick = Or(
        start_time >= 13 * 60,
        start_time < 14 * 60,
        start_time >= 14 * 60,
        start_time < 15 * 60
    )
    shirley = Or(
        start_time < 9 * 60,
        start_time >= 11 * 60,
        start_time < 12 * 60,
        start_time >= 14 * 60,
        start_time < 16 * 60
    )
    jeffrey = Or(
        start_time < 9 * 60,
        start_time >= 10 * 60,
        start_time < 11 * 60,
        start_time >= 13 * 60,
        start_time < 16 * 60
    )
    gloria = Or(
        start_time < 11 * 60,
        start_time >= 15 * 60,
        start_time < 15 * 60 + 30
    )
    nathan = Or(
        start_time < 9 * 60,
        start_time >= 10 * 60,
        start_time < 12 * 60,
        start_time >= 14 * 60,
        start_time < 17 * 60
    )
    angela = Or(
        start_time < 9 * 60,
        start_time >= 10 * 60,
        start_time < 11 * 60,
        start_time >= 12 * 60,
        start_time < 15 * 60,
        start_time >= 15 * 60,
        start_time < 16 * 60 + 30
    )
    david = Or(
        start_time < 9 * 60,
        start_time >= 10 * 60,
        start_time < 11 * 60,
        start_time >= 11 * 60,
        start_time < 14 * 60,
        start_time >= 14 * 60,
        start_time < 16 * 60
    )

    # Add participant constraints to the main constraints
    constraints.append(patrick)
    constraints.append(shirley)
    constraints.append(jeffrey)
    constraints.append(gloria)
    constraints.append(nathan)
    constraints.append(angela)
    constraints.append(david)

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_val = model[start_time].as_long()
        end_time_val = model[end_time].as_long()
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_time_val // 60:02d}:{start_time_val % 60:02d}\nEnd Time: {end_time_val // 60:02d}:{end_time_val % 60:02d}"
    else:
        return "No solution found"

print(find_meeting_time())