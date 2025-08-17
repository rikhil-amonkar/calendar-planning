import itertools
import json

names_list = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']

for names in itertools.permutations(names_list):
    # Check name constraints: Alice in house 1 (index 0), Eric in 2 (index 1), Peter in 3 (index 2)
    if names[0] != 'Alice' or names[1] != 'Eric' or names[2] != 'Peter':
        continue
    
    # Check Bob directly left of Arnold
    bob_pos = names.index('Bob')
    arnold_pos = names.index('Arnold')
    if arnold_pos != bob_pos + 1:
        continue
    
    # Now construct the vacations based on constraints
    vacations = [None] * 6
    # House 3 (index 2) is cultural
    vacations[2] = 'cultural'
    # House 4 (index 3) is city
    vacations[3] = 'city'
    # Bob's vacation is cruise
    bob_house = bob_pos
    vacations[bob_house] = 'cruise'
    # Beach must be in house 6 (index 5)
    vacations[5] = 'beach'
    # Remaining are mountain and camping for houses 1 and 2 (indices 0 and 1)
    # Assign mountain to 0, camping to 1
    vacations[0] = 'mountain'
    vacations[1] = 'camping'
    
    # Ensure all vacation types are unique
    if len(set(vacations)) != 6:
        continue
    
    # Build the solution
    solution_data = []
    for i in range(6):
        house_num = i + 1
        solution_data.append([str(house_num), names[i], vacations[i]])
    
    # Output JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": solution_data
        }
    }
    print(json.dumps(output))
    exit()

# If no solution found (though there should be one)
print(json.dumps({"solution": {"header": [], "rows": []}}))