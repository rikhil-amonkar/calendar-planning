import itertools
import json

def is_valid(houses):
    # Constraint 1: Alice is short
    for i in range(5):
        if houses[i][0] == 'Alice':
            if houses[i][1] != 'short':
                return False
            break
    else:
        return False

    # Constraint 3: average height not in house2 (index1)
    if houses[1][1] == 'average':
        return False

    # Constraint 4: average height left of stew
    i_avg = None
    i_stew = None
    for i in range(5):
        if houses[i][1] == 'average':
            i_avg = i
        if houses[i][2] == 'stew':
            i_stew = i
    if i_avg is None or i_stew is None:
        return False
    if i_avg >= i_stew:
        return False

    # Constraint 5: Arnold has stir fry
    for i in range(5):
        if houses[i][0] == 'Arnold':
            if houses[i][2] != 'stir fry':
                return False
            break
    else:
        return False

    # Constraint 8: Bob is right of Arnold
    i_arnold = None
    i_bob = None
    for i in range(5):
        if houses[i][0] == 'Arnold':
            i_arnold = i
        elif houses[i][0] == 'Bob':
            i_bob = i
    if i_arnold is None or i_bob is None:
        return False
    if i_arnold >= i_bob:
        return False

    # Constraint 9: grilled cheese is right of Eric (index2)
    for i in range(5):
        if houses[i][2] == 'grilled cheese':
            if i <= 2:
                return False
            break
    else:
        return False

    # Constraint 10: very short is left of Arnold
    i_vshort = None
    for i in range(5):
        if houses[i][1] == 'very short':
            i_vshort = i
            break
    if i_vshort is None:
        return False
    if i_vshort >= i_arnold:
        return False

    return True

def main():
    fixed_house = ('Eric', 'tall', 'pizza')
    names_list = ['Arnold', 'Bob', 'Alice', 'Peter']
    heights_list = ['very tall', 'average', 'short', 'very short']
    lunches_list = ['stew', 'grilled cheese', 'spaghetti', 'stir fry']
    
    found_solution = False
    solution_houses = None
    
    for names_perm in itertools.permutations(names_list):
        for heights_perm in itertools.permutations(heights_list):
            for lunches_perm in itertools.permutations(lunches_list):
                houses = [None] * 5
                houses[2] = fixed_house
                houses[0] = (names_perm[0], heights_perm[0], lunches_perm[0])
                houses[1] = (names_perm[1], heights_perm[1], lunches_perm[1])
                houses[3] = (names_perm[2], heights_perm[2], lunches_perm[2])
                houses[4] = (names_perm[3], heights_perm[3], lunches_perm[3])
                
                if is_valid(houses):
                    found_solution = True
                    solution_houses = houses
                    break
            if found_solution:
                break
        if found_solution:
            break
    
    if found_solution:
        header = ["House", "Name", "Height", "Lunch"]
        rows = []
        for i in range(5):
            house_num = str(i+1)
            name = solution_houses[i][0]
            height = solution_houses[i][1]
            lunch = solution_houses[i][2]
            rows.append([house_num, name, height, lunch])
        solution_dict = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()