import z3
import json

def main():
    names = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors = ['black', 'blonde', 'brown', 'red']
    
    house_name = [z3.Int(f'name_{i}') for i in range(4)]
    house_hair = [z3.Int(f'hair_{i}') for i in range(4)]
    
    solver = z3.Solver()
    
    for i in range(4):
        solver.add(house_name[i] >= 0, house_name[i] < 4)
        solver.add(house_hair[i] >= 0, house_hair[i] < 4)
    
    solver.add(z3.Distinct(house_name))
    solver.add(z3.Distinct(house_hair))
    
    # Clue 5: Alice is in first house
    alice_idx = names.index('Alice')
    solver.add(house_name[0] == alice_idx)
    
    # Clue 3: Eric has brown hair
    eric_idx = names.index('Eric')
    brown_idx = hair_colors.index('brown')
    for i in range(4):
        solver.add(z3.Implies(house_name[i] == eric_idx, house_hair[i] == brown_idx))
    
    # Clue 1: Eric directly left of blonde hair
    blonde_idx = hair_colors.index('blonde')
    for i in range(3):
        solver.add(z3.Implies(house_name[i] == eric_idx, house_hair[i+1] == blonde_idx))
    
    # Clue 2: Alice and Arnold are adjacent (corrected)
    arnold_idx = names.index('Arnold')
    adjacent_constraints = []
    for i in range(3):
        adjacent_constraints.append(z3.And(house_name[i] == alice_idx, house_name[i+1] == arnold_idx))
        adjacent_constraints.append(z3.And(house_name[i] == arnold_idx, house_name[i+1] == alice_idx))
    solver.add(z3.Or(adjacent_constraints))
    
    # Clue 4: Black hair not in first house
    black_idx = hair_colors.index('black')
    solver.add(house_hair[0] != black_idx)
    
    if solver.check() == z3.sat:
        model = solver.model()
        rows = []
        for i in range(4):
            name_val = model.eval(house_name[i]).as_long()
            hair_val = model.eval(house_hair[i]).as_long()
            rows.append([str(i+1), names[name_val], hair_colors[hair_val]])
        solution = {"solution": {"header": ["House", "Name", "HairColor"], "rows": rows}}
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()