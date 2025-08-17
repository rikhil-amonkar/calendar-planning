import itertools
import json

# Define the possible values
names = ['Peter', 'Eric', 'Arnold']
education = ['bachelor', 'associate', 'high school']
occupation = ['teacher', 'doctor', 'engineer']

solution_found = None

# Generate all possible permutations for each category
for name_perm in itertools.permutations(names):
    for edu_perm in itertools.permutations(education):
        for occ_perm in itertools.permutations(occupation):
            # Check clue 3: Peter has high school diploma
            peter_index = name_perm.index('Peter')
            if edu_perm[peter_index] != 'high school':
                continue

            # Check clue 4: doctor has bachelor's degree
            valid_doctor = True
            for i in range(3):
                if occ_perm[i] == 'doctor':
                    if edu_perm[i] != 'bachelor':
                        valid_doctor = False
                        break
            if not valid_doctor:
                continue

            # Check clue 1: teacher is directly left of associate
            teacher_pos = None
            for i in range(3):
                if occ_perm[i] == 'teacher':
                    teacher_pos = i
                    break
            if teacher_pos not in [0, 1]:
                continue
            associate_pos = teacher_pos + 1
            if edu_perm[associate_pos] != 'associate':
                continue

            # Check clue 2: associate and Eric are next to each other
            a_pos = edu_perm.index('associate')
            adjacent = False
            if a_pos == 0:
                if name_perm[a_pos + 1] == 'Eric':
                    adjacent = True
            elif a_pos == 1:
                if name_perm[a_pos - 1] == 'Eric' or name_perm[a_pos + 1] == 'Eric':
                    adjacent = True
            else:  # a_pos == 2
                if name_perm[a_pos - 1] == 'Eric':
                    adjacent = True
            if not adjacent:
                continue

            # All constraints are satisfied
            solution_found = []
            for i in range(3):
                house_num = str(i + 1)
                solution_found.append([house_num, name_perm[i], edu_perm[i], occ_perm[i]])
            break  # exit the occ_perm loop
        if solution_found:
            break  # exit edu_perm loop
    if solution_found:
        break  # exit name_perm loop

# Prepare the JSON output
json_output = {
    "solution": {
        "header": ["House", "Name", "Education", "Occupation"],
        "rows": solution_found
    }
}

# Print the JSON output
print(json.dumps(json_output, indent=2))