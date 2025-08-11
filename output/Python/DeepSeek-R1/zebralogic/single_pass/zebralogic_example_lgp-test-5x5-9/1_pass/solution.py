import json
import copy

def main():
    attributes = ['name', 'drink', 'color', 'flower', 'hobby']
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']
    
    domains = {
        'name': [set(names) for _ in range(5)],
        'drink': [set(drinks) for _ in range(5)],
        'color': [set(colors) for _ in range(5)],
        'flower': [set(flowers) for _ in range(5)],
        'hobby': [set(hobbies) for _ in range(5)]
    }
    
    domains['color'][1] = {'white'}
    domains['flower'][1] = {'roses'}
    domains['drink'][2] = {'water'}
    domains['name'][2] = {'Peter'}
    
    domains['name'][3] = domains['name'][3] - {'Alice'}
    
    for attr in domains:
        for i in range(5):
            if len(domains[attr][i]) == 1:
                val = next(iter(domains[attr][i]))
                for j in range(5):
                    if j != i and val in domains[attr][j]:
                        domains[attr][j].remove(val)
    
    def all_different(domains):
        for attr in attributes:
            fixed_vals = {}
            for i in range(5):
                if len(domains[attr][i]) == 1:
                    val = next(iter(domains[attr][i]))
                    if val in fixed_vals:
                        return None
                    fixed_vals[val] = i
            for i in range(5):
                if len(domains[attr][i]) > 1:
                    to_remove = []
                    for val in domains[attr][i]:
                        if val in fixed_vals and fixed_vals[val] != i:
                            to_remove.append(val)
                    for val in to_remove:
                        domains[attr][i].remove(val)
        return domains

    def propagate_equivalence(domains):
        for i in range(5):
            if 'green' in domains['color'][i]:
                if 'coffee' in domains['drink'][i]:
                    domains['drink'][i] = {'coffee'}
                if 'lilies' in domains['flower'][i]:
                    domains['flower'][i] = {'lilies'}
            if 'coffee' in domains['drink'][i]:
                if 'green' in domains['color'][i]:
                    domains['color'][i] = {'green'}
                if 'lilies' in domains['flower'][i]:
                    domains['flower'][i] = {'lilies'}
            if 'lilies' in domains['flower'][i]:
                if 'green' in domains['color'][i]:
                    domains['color'][i] = {'green'}
                if 'coffee' in domains['drink'][i]:
                    domains['drink'][i] = {'coffee'}
            
            if 'carnations' in domains['flower'][i]:
                if 'root beer' in domains['drink'][i]:
                    domains['drink'][i] = {'root beer'}
                if 'gardening' in domains['hobby'][i]:
                    domains['hobby'][i] = {'gardening'}
            if 'root beer' in domains['drink'][i]:
                if 'carnations' in domains['flower'][i]:
                    domains['flower'][i] = {'carnations'}
                if 'gardening' in domains['hobby'][i]:
                    domains['hobby'][i] = {'gardening'}
            if 'gardening' in domains['hobby'][i]:
                if 'root beer' in domains['drink'][i]:
                    domains['drink'][i] = {'root beer'}
                if 'carnations' in domains['flower'][i]:
                    domains['flower'][i] = {'carnations'}
            
            if 'cooking' in domains['hobby'][i]:
                if 'blue' in domains['color'][i]:
                    domains['color'][i] = {'blue'}
            if 'blue' in domains['color'][i]:
                if 'cooking' in domains['hobby'][i]:
                    domains['hobby'][i] = {'cooking'}
        
        for i in range(5):
            if 'green' not in domains['color'][i]:
                if 'coffee' in domains['drink'][i]:
                    domains['drink'][i].discard('coffee')
                if 'lilies' in domains['flower'][i]:
                    domains['flower'][i].discard('lilies')
            if 'coffee' not in domains['drink'][i]:
                if 'green' in domains['color'][i]:
                    domains['color'][i].discard('green')
                if 'lilies' in domains['flower'][i]:
                    domains['flower'][i].discard('lilies')
            if 'lilies' not in domains['flower'][i]:
                if 'green' in domains['color'][i]:
                    domains['color'][i].discard('green')
                if 'coffee' in domains['drink'][i]:
                    domains['drink'][i].discard('coffee')
            
            if 'carnations' not in domains['flower'][i]:
                if 'root beer' in domains['drink'][i]:
                    domains['drink'][i].discard('root beer')
                if 'gardening' in domains['hobby'][i]:
                    domains['hobby'][i].discard('gardening')
            if 'root beer' not in domains['drink'][i]:
                if 'carnations' in domains['flower'][i]:
                    domains['flower'][i].discard('carnations')
                if 'gardening' in domains['hobby'][i]:
                    domains['hobby'][i].discard('gardening')
            if 'gardening' not in domains['hobby'][i]:
                if 'root beer' in domains['drink'][i]:
                    domains['drink'][i].discard('root beer')
                if 'carnations' in domains['flower'][i]:
                    domains['flower'][i].discard('carnations')
            
            if 'cooking' not in domains['hobby'][i]:
                if 'blue' in domains['color'][i]:
                    domains['color'][i].discard('blue')
            if 'blue' not in domains['color'][i]:
                if 'cooking' in domains['hobby'][i]:
                    domains['hobby'][i].discard('cooking')
        return domains

    def search(domains):
        domains = all_different(domains)
        if domains is None:
            return None
        domains = propagate_equivalence(domains)
        if domains is None:
            return None
        
        changed = True
        while changed:
            changed = False
            for attr in attributes:
                for i in range(5):
                    if len(domains[attr][i]) == 0:
                        return None
                    if len(domains[attr][i]) == 1:
                        val = next(iter(domains[attr][i]))
                        for j in range(5):
                            if j != i and val in domains[attr][j]:
                                domains[attr][j].remove(val)
                                changed = True
            if changed:
                domains = all_different(domains)
                if domains is None:
                    return None
                domains = propagate_equivalence(domains)
                if domains is None:
                    return None
        return domains

    def check_solution(assignment):
        names = [assignment['name'][i] for i in range(5)]
        drinks = [assignment['drink'][i] for i in range(5)]
        colors = [assignment['color'][i] for i in range(5)]
        flowers = [assignment['flower'][i] for i in range(5)]
        hobbies = [assignment['hobby'][i] for i in range(5)]
        
        if names[3] == 'Alice':
            return False
        for i in range(5):
            if drinks[i] == 'root beer':
                if hobbies[i] != 'gardening':
                    return False
            if colors[i] == 'green':
                if drinks[i] != 'coffee':
                    return False
                if flowers[i] != 'lilies':
                    return False
        daffodil_house = None
        blue_house = None
        for i in range(5):
            if flowers[i] == 'daffodils':
                daffodil_house = i
            if colors[i] == 'blue':
                blue_house = i
        if daffodil_house is not None and blue_house is not None:
            if blue_house <= daffodil_house:
                return False
        for i in range(5):
            if hobbies[i] == 'cooking':
                if colors[i] != 'blue':
                    return False
        if 'Eric' in names:
            eric_index = names.index('Eric')
            if eric_index == 4:
                return False
            if drinks[eric_index + 1] != 'tea':
                return False
        for i in range(5):
            if drinks[i] == 'water':
                if names[i] != 'Peter':
                    return False
        if 'Arnold' in names:
            arnold_index = names.index('Arnold')
            if hobbies[arnold_index] != 'photography':
                return False
        for i in range(5):
            if colors[i] == 'white':
                if flowers[i] != 'roses':
                    return False
        carnation_house = None
        red_house = None
        for i in range(5):
            if flowers[i] == 'carnations':
                carnation_house = i
            if colors[i] == 'red':
                red_house = i
        if carnation_house is not None and red_house is not None:
            if abs(carnation_house - red_house) != 2:
                return False
        cooking_index = None
        painting_index = None
        for i in range(5):
            if hobbies[i] == 'cooking':
                cooking_index = i
            if hobbies[i] == 'painting':
                painting_index = i
        if cooking_index is not None and painting_index is not None:
            if cooking_index >= painting_index:
                return False
        if drinks[2] != 'water':
            return False
        for i in range(5):
            if flowers[i] == 'carnations':
                if drinks[i] != 'root beer':
                    return False
        if colors[1] != 'white':
            return False
        return True

    def solve(domains):
        branches = []
        if 'Eric' in domains['name'][0] and 'tea' in domains['drink'][1]:
            branch = copy.deepcopy(domains)
            branch['name'][0] = {'Eric'}
            branch['drink'][1] = {'tea'}
            for i in range(5):
                if i != 0:
                    if 'Eric' in branch['name'][i]:
                        branch['name'][i].remove('Eric')
                if i != 1:
                    if 'tea' in branch['drink'][i]:
                        branch['drink'][i].remove('tea')
            branches.append(('A', branch))
        if 'Eric' in domains['name'][3] and 'tea' in domains['drink'][4]:
            branch = copy.deepcopy(domains)
            branch['name'][3] = {'Eric'}
            branch['drink'][4] = {'tea'}
            for i in range(5):
                if i != 3:
                    if 'Eric' in branch['name'][i]:
                        branch['name'][i].remove('Eric')
                if i != 4:
                    if 'tea' in branch['drink'][i]:
                        branch['drink'][i].remove('tea')
            branches.append(('B', branch))
        
        for label, branch in branches:
            branch = all_different(branch)
            branch = propagate_equivalence(branch)
            if branch is None:
                continue
            
            branch['color'][2] = {'red'}
            for i in range(5):
                if i != 2 and 'red' in branch['color'][i]:
                    branch['color'][i].remove('red')
            
            sub_branches = []
            if 'carnations' in branch['flower'][0]:
                sub_branch = copy.deepcopy(branch)
                sub_branch['flower'][0] = {'carnations'}
                for i in range(5):
                    if i != 0 and 'carnations' in sub_branch['flower'][i]:
                        sub_branch['flower'][i].remove('carnations')
                sub_branches.append(('A1', sub_branch))
            if 'carnations' in branch['flower'][4]:
                sub_branch = copy.deepcopy(branch)
                sub_branch['flower'][4] = {'carnations'}
                for i in range(5):
                    if i != 4 and 'carnations' in sub_branch['flower'][i]:
                        sub_branch['flower'][i].remove('carnations')
                sub_branches.append(('A2', sub_branch))
            
            for sub_label, sub_branch in sub_branches:
                sub_branch = all_different(sub_branch)
                sub_branch = propagate_equivalence(sub_branch)
                if sub_branch is None:
                    continue
                
                result = search(sub_branch)
                if result is None:
                    continue
                if any(len(result[attr][i]) != 1 for attr in attributes for i in range(5)):
                    continue
                
                assignment = {attr: [next(iter(result[attr][i])) for i in range(5)] for attr in attributes}
                if check_solution(assignment):
                    return assignment
        return None

    assignment = solve(domains)
    if assignment is None:
        print('{"error": "No solution found"}')
        return

    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": []
        }
    }
    for i in range(5):
        house = str(i+1)
        name = assignment['name'][i]
        drink = assignment['drink'][i]
        color = assignment['color'][i]
        flower = assignment['flower'][i]
        hobby = assignment['hobby'][i]
        solution['solution']['rows'].append([house, name, drink, color, flower, hobby])
    
    print(json.dumps(solution))

if __name__ == "__main__":
    main()