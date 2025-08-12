import json

def solve_puzzle():
    # Define the possible people and their preferences
    people = ['Arnold', 'Eric']
    vacations = ['beach', 'mountain']
    
    # Initialize the solution list
    solutions = []
    
    # Try all permutations of people in houses
    for i in range(len(people)):
        for j in range(len(people)):
            if i != j:  # Ensure different people in different houses
                person_house_1 = people[i]
                person_house_2 = people[j]
                
                # Try all permutations of vacations
                for k in range(len(vacations)):
                    for l in range(len(vacations)):
                        if k != l:  # Ensure different vacations for different houses
                            vacation_house_1 = vacations[k]
                            vacation_house_2 = vacations[l]
                            
                            # Check the clue: Arnold is somewhere to the right of the person who loves beach vacations
                            if (person_house_2 == 'Arnold' and vacation_house_1 == 'beach') or \
                               (person_house_1 != 'Arnold' and vacation_house_2 == 'beach'):
                                # If the clue is satisfied, add this configuration to the solutions
                                solutions.append([
                                    ["1", person_house_1, vacation_house_1],
                                    ["2", person_house_2, vacation_house_2]
                                ])
    
    # Format the solution as required
    formatted_solution = {
        "solution": {
            "header": ["House", "Name", "vacation"],
            "rows": solutions[0]  # There should be only one valid solution
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(formatted_solution))

# Run the function to solve the puzzle
solve_puzzle()