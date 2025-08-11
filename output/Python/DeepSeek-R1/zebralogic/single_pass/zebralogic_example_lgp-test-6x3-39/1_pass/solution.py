import json

def check_unary_constraints(index, name, child, smoothie):
    if name == 'Alice':
        if child != 'Alice':
            return False
        if smoothie != 'watermelon':
            return False
    if child == 'Alice':
        if name != 'Alice':
            return False
    if name == 'Bob':
        if child != 'Timothy':
            return False
    if child == 'Timothy':
        if name != 'Bob':
            return False
    if index == 4:
        if name == 'Alice':
            return False
    if index == 1:
        if child == 'Samantha':
            return False
        if name == 'Arnold':
            return False
    if child == 'Meredith':
        return False
    if smoothie == 'dragonfruit':
        return False
    if smoothie == 'watermelon':
        if name != 'Alice':
            return False
    return True

def check_binary_constraints(name_positions, child_positions, smoothie_positions):
    if 'Fred' in child_positions and 'desert' in smoothie_positions:
        if abs(child_positions['Fred'] - smoothie_positions['desert']) != 1:
            return False
    if 'blueberry' in smoothie_positions and 'Fred' in child_positions:
        if smoothie_positions['blueberry'] >= child_positions['Fred']:
            return False
    if 'cherry' in smoothie_positions and 'watermelon' in smoothie_positions:
        if smoothie_positions['cherry'] >= smoothie_positions['watermelon']:
            return False
    if 'Peter' in name_positions and 'Samantha' in child_positions:
        if name_positions['Peter'] <= child_positions['Samantha']:
            return False
    if 'Arnold' in name_positions and 'Carol' in name_positions:
        if name_positions['Arnold'] != name_positions['Carol'] - 1:
            return False
    if 'cherry' in smoothie_positions and 'Samantha' in child_positions:
        if smoothie_positions['cherry'] != child_positions['Samantha'] - 1:
            return False
    return True

def backtrack(index, state, available_names, available_children, available_smoothies, name_positions, child_positions, smoothie_positions):
    if index == 5:
        return state
    for name in available_names:
        for child in available_children:
            for smoothie in available_smoothies:
                if not check_unary_constraints(index, name, child, smoothie):
                    continue
                new_avail_names = available_names - {name}
                new_avail_children = available_children - {child}
                new_avail_smoothies = available_smoothies - {smoothie}
                new_state = state[:]
                new_state[index] = (name, child, smoothie)
                new_name_pos = name_positions.copy()
                new_child_pos = child_positions.copy()
                new_smoothie_pos = smoothie_positions.copy()
                new_name_pos[name] = index
                new_child_pos[child] = index
                new_smoothie_pos[smoothie] = index
                if not check_binary_constraints(new_name_pos, new_child_pos, new_smoothie_pos):
                    continue
                res = backtrack(index+1, new_state, new_avail_names, new_avail_children, new_avail_smoothies, new_name_pos, new_child_pos, new_smoothie_pos)
                if res is not None:
                    return res
    return None

names = ['Arnold','Peter','Carol','Alice','Bob','Eric']
children = ['Alice','Timothy','Bella','Meredith','Fred','Samantha']
smoothies = ['desert','cherry','watermelon','blueberry','lime','dragonfruit']

solution_found = None
for name6 in names:
    state = [None] * 6
    state[5] = (name6, 'Meredith', 'dragonfruit')
    avail_names = set(names) - {name6}
    avail_children = set(children) - {'Meredith'}
    avail_smoothies = set(smoothies) - {'dragonfruit'}
    name_pos = {name6: 5}
    child_pos = {'Meredith': 5}
    smoothie_pos = {'dragonfruit': 5}
    sol = backtrack(0, state, avail_names, avail_children, avail_smoothies, name_pos, child_pos, smoothie_pos)
    if sol is not None:
        solution_found = sol
        break

if solution_found is None:
    print(json.dumps({"error": "No solution found"}))
else:
    header = ["House", "Name", "Child", "Smoothie"]
    rows = []
    for i in range(6):
        house_num = str(i+1)
        name_val, child_val, smoothie_val = solution_found[i]
        rows.append([house_num, name_val, child_val, smoothie_val])
    output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output))