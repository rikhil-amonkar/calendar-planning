import itertools
import json

# Generate possible name permutations with fixed positions (Alice in 1, Eric in 2, Peter in 3)
remaining_names = ['Bob', 'Carol', 'Arnold']
name_perms = []
for p in itertools.permutations(remaining_names):
    names = ['Alice', 'Eric', 'Peter'] + list(p)
    name_perms.append(names)

# Generate possible vacation permutations with fixed positions (cultural in 3, city in 4)
remaining_vacations = ['mountain', 'camping', 'cruise', 'beach']
vac_perms = []
for p in itertools.permutations(remaining_vacations):
    vac = [p[0], p[1], 'cultural', 'city', p[2], p[3]]
    vac_perms.append(vac)

solution_found = None

for names in name_perms:
    for vacs in vac_perms:
        # Check Bob is directly left of Arnold
        try:
            bob_idx = names.index('Bob')
            arnold_idx = names.index('Arnold')
        except ValueError:
            continue
        if arnold_idx != bob_idx + 1:
            continue
        
        # Check Bob's vacation is cruise
        if vacs[bob_idx] != 'cruise':
            continue
        
        # Check camping not in first house
        if vacs[0] == 'camping':
            continue
        
        # Check beach is in house 5 or 6 (index 4 or 5)
        if vacs[4] != 'beach' and vacs[5] != 'beach':
            continue
        
        # All constraints satisfied
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": []
            }
        }
        for i in range(6):
            house_num = str(i + 1)
            solution["solution"]["rows"].append([house_num, names[i], vacs[i]])
        solution_found = solution
        break
    if solution_found:
        break

# Output JSON
print(json.dumps(solution_found))