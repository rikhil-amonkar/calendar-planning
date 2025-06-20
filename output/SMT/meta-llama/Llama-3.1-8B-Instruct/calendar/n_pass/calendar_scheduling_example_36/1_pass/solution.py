from z3 import *

def schedule_meeting(ryan_availability, ruth_availability, denise_availability, max_duration, preferences=None):
    # Create Z3 variables
    day = [Bool('day_' + str(i)) for i in range(7)]
    start_time = [Int('start_time_' + str(i)) for i in range(7)]
    end_time = [Int('end_time_' + str(i)) for i in range(7)]

    # Define the constraints
    constraints = []
    for i in range(7):
        # Ensure the start time is within the work hours
        constraints.append(And(9 <= start_time[i], start_time[i] <= 17))
        constraints.append(And(end_time[i] >= start_time[i], end_time[i] <= 17))
        constraints.append(And(end_time[i] - start_time[i] == max_duration))
        
        # Ensure the meeting time is on the correct day
        constraints.append(Implies(day[i], start_time[i] >= 9))
        constraints.append(Implies(day[i], end_time[i] <= 17))

        # Ensure the meeting time does not conflict with the participants' availability
        for participant, availability in zip([ryan_availability, ruth_availability, denise_availability], [ryan_availability, ruth_availability, denise_availability]):
            for availability_start, availability_end in availability:
                constraints.append(Or(Not(day[i]), Not(And(start_time[i] >= availability_start, start_time[i] < availability_end))))
                constraints.append(Or(Not(day[i]), Not(And(end_time[i] > availability_start, end_time[i] <= availability_end))))

        # Apply any additional preferences
        if preferences is not None:
            for preference in preferences:
                if preference['day'] == i:
                    constraints.append(And(start_time[i] >= preference['start_time'], start_time[i] <= preference['end_time']))

    # Define the objective function
    objective = Or(*[day[i] for i in range(7)])

    # Solve the problem
    solver = Solver()
    solver.add(constraints)
    solver.add(objective)

    # Check if a solution exists
    if solver.check() == sat:
        # Extract the solution
        model = solver.model()
        solution_day = [model.evaluate(day[i]).as_bool() for i in range(7)]
        solution_start_time = [model.evaluate(start_time[i]).as_int() for i in range(7)]
        solution_end_time = [model.evaluate(end_time[i]).as_int() for i in range(7)]

        # Find the first solution that satisfies all constraints
        solution = next((i for i in range(7) if solution_day[i] and solution_start_time[i] == 9 and solution_end_time[i] == 10), None)

        # Return the solution
        return f"SOLUTION:\nDay: Monday\nStart Time: {solution_start_time[solution]:02d}:00\nEnd Time: {solution_end_time[solution]:02d}:00"
    else:
        return "No solution exists"

# Example usage
ryan_availability = [(9, 9.5), (12.5, 13)]
ruth_availability = []
denise_availability = [(9.5, 10.5), (12, 13), (14.5, 16.5)]
max_duration = 1
preferences = [{'day': 0,'start_time': 10.5, 'end_time': 12}]
print(schedule_meeting(ryan_availability, ruth_availability, denise_availability, max_duration, preferences))