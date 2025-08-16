import itertools
import json

def check_clue6(candidate):
    g = None
    a = None
    for i in range(3):
        if candidate[i][4] == 'gardening':
            g = i
        if candidate[i][2] == 'associate':
            a = i
    if g is None or a is None:
        return False
    return a > g

def check_clue9(candidate):
    for i in range(3):
        if candidate[i][4] == 'photography':
            return candidate[i][1] == 'teacher'
    return False

def main():
    names = ['Arnold', 'Peter', 'Eric']
    smoothies = ['watermelon', 'desert', 'cherry']
    occ_options = [('engineer', 'teacher'), ('teacher', 'engineer')]
    edu_domain = ['associate', 'high school', 'bachelor']
    hob_options = [('gardening', 'photography'), ('photography', 'gardening')]
    
    found_solution = None
    for occ_pair in occ_options:
        occ0, occ2 = occ_pair
        for edu_perm in itertools.permutations(edu_domain):
            if edu_perm[2] != 'bachelor':
                continue
            for hob_pair in hob_options:
                hob0, hob2 = hob_pair
                candidate = [
                    [names[0], occ0, edu_perm[0], smoothies[0], hob0],
                    [names[1], 'doctor', edu_perm[1], smoothies[1], 'cooking'],
                    [names[2], occ2, edu_perm[2], smoothies[2], hob2]
                ]
                if check_clue6(candidate) and check_clue9(candidate):
                    found_solution = candidate
                    break
            if found_solution:
                break
        if found_solution:
            break
    
    if found_solution is None:
        print(json.dumps({"error": "No solution found"}))
        return
    
    header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
    rows = []
    for i in range(3):
        house_data = found_solution[i]
        row = [str(i+1)] + house_data
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()