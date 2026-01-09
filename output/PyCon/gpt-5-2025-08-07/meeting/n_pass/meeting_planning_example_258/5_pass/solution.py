from constraint import Problem

def create_exercise_plan():
    # Define the minimum durations for each person
    betty_min = 20
    david_min = 25
    barbara_min = 15
    
    # Create the constraint problem
    problem = Problem()
    
    # Define the order of people
    people = ['betty', 'david', 'barbara']
    min_durations = [betty_min, david_min, barbara_min]
    
    # Add variables for each person's duration
    for i, person in enumerate(people):
        problem.addVariable(f'{person}_duration', range(min_durations[i], 61))
    
    # Add constraint: total duration must be exactly 60 minutes
    problem.addConstraint(
        lambda betty, david, barbara: betty + david + barbara == 60,
        ['betty_duration', 'david_duration', 'barbara_duration']
    )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Use the first valid solution
        solution = solutions[0]
        
        # Extract the durations
        betty_duration = solution['betty_duration']
        david_duration = solution['david_duration']
        barbara_duration = solution['barbara_duration']
        total = betty_duration + david_duration + barbara_duration
        
        # Verify all constraints are satisfied
        constraints_satisfied = (
            betty_duration >= betty_min and
            david_duration >= david_min and
            barbara_duration >= barbara_min and
            total == 60
        )
        
        if constraints_satisfied:
            # Format the output as requested
            plan = {
                "betty": betty_duration,
                "david": david_duration, 
                "barbara": barbara_duration,
                "total": total
            }
            return plan
        else:
            return None
    else:
        return None

# Generate and display the exercise plan
plan = create_exercise_plan()

if plan:
    print("Valid plan found!")
    print("\nExercise schedule:")
    print("=" * 30)
    print(f"Betty: {plan['betty']} minutes")
    print(f"David: {plan['david']} minutes") 
    print(f"Barbara: {plan['barbara']} minutes")
    print("=" * 30)
    print(f"Total: {plan['total']} minutes")
    
    # Verify constraints
    print("\nConstraint verification:")
    print(f"- Betty ≥ 20 minutes: {plan['betty'] >= 20}")
    print(f"- David ≥ 25 minutes: {plan['david'] >= 25}")
    print(f"- Barbara ≥ 15 minutes: {plan['barbara'] >= 15}")
    print(f"- Total = 60 minutes: {plan['total'] == 60}")
else:
    print("No valid plan found that satisfies all constraints.")