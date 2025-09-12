import itertools

# Define the people, hobbies and occupations
people = ['Alice', 'Bob', 'Charlie', 'Diana']
hobbies = ['photography', 'gardening', 'cooking', 'painting']
occupations = ['teacher', 'engineer', 'doctor', 'artist']

# Generate all possible assignments
all_hobby_assignments = list(itertools.permutations(hobbies))
all_occupation_assignments = list(itertools.permutations(occupations))

# Find valid combinations that satisfy the constraint
valid_solutions = []

for hobby_assignment in all_hobby_assignments:
    for occupation_assignment in all_occupation_assignments:
        # Check the constraint: photography hobby == teacher occupation for each person
        valid = True
        for i in range(len(people)):
            has_photography = (hobby_assignment[i] == 'photography')
            is_teacher = (occupation_assignment[i] == 'teacher')
            
            # The constraint: (hobby is photography) == (occupation is teacher)
            if has_photography != is_teacher:
                valid = False
                break
        
        if valid:
            valid_solutions.append((hobby_assignment, occupation_assignment))

# Print the solutions
if valid_solutions:
    print("Valid solutions found:")
    for i, (hobby_assign, occup_assign) in enumerate(valid_solutions, 1):
        print(f"\nSolution {i}:")
        for j, person in enumerate(people):
            print(f"  {person}: Hobby = {hobby_assign[j]}, Occupation = {occup_assign[j]}")
else:
    print("No valid solutions found")