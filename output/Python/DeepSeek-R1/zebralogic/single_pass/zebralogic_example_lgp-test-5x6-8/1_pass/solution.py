import json

def main():
    attributes = {
        'Name': ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice'],
        'HouseStyle': ['modern', 'craftsman', 'ranch', 'victorian', 'colonial'],
        'Mother': ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya'],
        'PhoneModel': ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21'],
        'Drink': ['coffee', 'water', 'root beer', 'tea', 'milk'],
        'Animal': ['fish', 'dog', 'horse', 'bird', 'cat']
    }
    
    attribute_names = ['Name', 'HouseStyle', 'Mother', 'PhoneModel', 'Drink', 'Animal']
    attr_index_map = {attr: idx for idx, attr in enumerate(attribute_names)}
    
    grid = []
    for _ in range(5):
        row = []
        for attr in attribute_names:
            row.append(set(attributes[attr]))
        grid.append(row)
    
    def enforce_uniqueness(grid):
        changed = False
        for attr_idx in range(len(attribute_names)):
            for house_i in range(5):
                if len(grid[house_i][attr_idx]) == 1:
                    val = next(iter(grid[house_i][attr_idx]))
                    for other_house in range(5):
                        if other_house != house_i:
                            if val in grid[other_house][attr_idx]:
                                grid[other_house][attr_idx].remove(val)
                                changed = True
        return changed

    def make_same_house_constraint(attr1, value1, attr2, value2):
        idx1 = attr_index_map[attr1]
        idx2 = attr_index_map[attr2]
        def constraint_func(grid):
            changed = False
            for i in range(5):
                if value1 in grid[i][idx1] and value2 not in grid[i][idx2]:
                    grid[i][idx1].remove(value1)
                    changed = True
                if value2 in grid[i][idx2] and value1 not in grid[i][idx1]:
                    grid[i][idx2].remove(value2)
                    changed = True
            houses1 = set()
            houses2 = set()
            for i in range(5):
                if value1 in grid[i][idx1]:
                    houses1.add(i)
                if value2 in grid[i][idx2]:
                    houses2.add(i)
            for i in range(5):
                if i not in houses2 and value1 in grid[i][idx1]:
                    grid[i][idx1].remove(value1)
                    changed = True
                if i not in houses1 and value2 in grid[i][idx2]:
                    grid[i][idx2].remove(value2)
                    changed = True
            return changed
        return constraint_func

    def make_absolute_position(attr, value, house_number):
        house_index = house_number - 1
        attr_index = attr_index_map[attr]
        def constraint_func(grid):
            if value not in grid[house_index][attr_index]:
                return False
            if len(grid[house_index][attr_index]) == 1:
                return False
            grid[house_index][attr_index] = {value}
            return True
        return constraint_func

    def make_different_house(attr, value, house_number):
        house_index = house_number - 1
        attr_index = attr_index_map[attr]
        def constraint_func(grid):
            if value in grid[house_index][attr_index]:
                grid[house_index][attr_index].remove(value)
                return True
            return False
        return constraint_func

    def make_relative_position(attr1, value1, attr2, value2, relation):
        idx1 = attr_index_map[attr1]
        idx2 = attr_index_map[attr2]
        def constraint_func(grid):
            changed = False
            houses1 = []
            houses2 = []
            for i in range(5):
                if value1 in grid[i][idx1]:
                    houses1.append(i)
                if value2 in grid[i][idx2]:
                    houses2.append(i)
            if relation == 'right':
                for i in houses1:
                    found = False
                    for j in houses2:
                        if j < i:
                            found = True
                            break
                    if not found:
                        if value1 in grid[i][idx1]:
                            grid[i][idx1].remove(value1)
                            changed = True
                for i in houses2:
                    found = False
                    for j in houses1:
                        if j > i:
                            found = True
                            break
                    if not found:
                        if value2 in grid[i][idx2]:
                            grid[i][idx2].remove(value2)
                            changed = True
            elif relation == 'left':
                for i in houses1:
                    found = False
                    for j in houses2:
                        if j > i:
                            found = True
                            break
                    if not found:
                        if value1 in grid[i][idx1]:
                            grid[i][idx1].remove(value1)
                            changed = True
                for i in houses2:
                    found = False
                    for j in houses1:
                        if j < i:
                            found = True
                            break
                    if not found:
                        if value2 in grid[i][idx2]:
                            grid[i][idx2].remove(value2)
                            changed = True
            return changed
        return constraint_func

    constraints = [
        make_different_house('PhoneModel', 'google pixel 6', 1),
        make_same_house_constraint('Drink', 'water', 'Name', 'Alice'),
        make_relative_position('HouseStyle', 'colonial', 'PhoneModel', 'huawei p50', 'right'),
        make_same_house_constraint('Animal', 'horse', 'PhoneModel', 'oneplus 9'),
        make_same_house_constraint('HouseStyle', 'ranch', 'Mother', 'Kailyn'),
        make_same_house_constraint('Drink', 'root beer', 'Animal', 'cat'),
        make_different_house('HouseStyle', 'colonial', 4),
        make_absolute_position('Animal', 'bird', 4),
        make_same_house_constraint('Drink', 'tea', 'Name', 'Bob'),
        make_relative_position('Drink', 'tea', 'Mother', 'Kailyn', 'right'),
        make_relative_position('Drink', 'root beer', 'Mother', 'Kailyn', 'left'),
        make_same_house_constraint('Animal', 'horse', 'HouseStyle', 'modern'),
        make_same_house_constraint('PhoneModel', 'iphone 13', 'Drink', 'milk'),
        make_same_house_constraint('Animal', 'dog', 'Drink', 'milk'),
        make_same_house_constraint('PhoneModel', 'google pixel 6', 'HouseStyle', 'craftsman'),
        make_different_house('Name', 'Eric', 2),
        make_absolute_position('Drink', 'tea', 4),
        make_absolute_position('Animal', 'horse', 3),
        make_same_house_constraint('HouseStyle', 'modern', 'Mother', 'Penny'),
        make_same_house_constraint('Drink', 'root beer', 'Name', 'Peter'),
        make_different_house('Mother', 'Aniya', 4),
        make_same_house_constraint('Mother', 'Janelle', 'Drink', 'water')
    ]

    max_iter = 1000
    iter_count = 0
    changed = True
    while changed and iter_count < max_iter:
        changed = False
        changed = enforce_uniqueness(grid) or changed
        for constraint in constraints:
            changed = constraint(grid) or changed
        iter_count += 1

    for i in range(5):
        for j in range(6):
            if len(grid[i][j]) != 1:
                raise RuntimeError(f"Solution not found: house {i+1} attribute {attribute_names[j]} has possibilities: {grid[i][j]}")
    
    output_rows = []
    for i in range(5):
        row = [str(i+1)]
        for j in range(6):
            row.append(next(iter(grid[i][j])))
        output_rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
            "rows": output_rows
        }
    }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()