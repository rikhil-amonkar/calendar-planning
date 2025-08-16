import json
import copy

def main():
    attributes = ['name', 'house_style', 'food', 'vacation', 'height', 'cigar']
    domains = {
        'name': ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice'],
        'house_style': ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian'],
        'food': ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup'],
        'vacation': ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach'],
        'height': ['average', 'very tall', 'very short', 'short', 'tall', 'super tall'],
        'cigar': ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']
    }
    
    assignment = [[None for _ in range(len(attributes))] for _ in range(6)]
    var_domains = [[copy.deepcopy(domains[attr]) for attr in attributes] for _ in range(6)]
    
    assignment[3][0] = 'Eric'
    assignment[4][0] = 'Alice'
    assignment[4][2] = 'spaghetti'
    assignment[4][1] = 'victorian'
    
    for i in range(6):
        for j, attr in enumerate(attributes):
            if assignment[i][j] is not None:
                val = assignment[i][j]
                var_domains[i][j] = [val]
                for ii in range(6):
                    if ii != i and val in var_domains[ii][j]:
                        var_domains[ii][j].remove(val)
    
    unary_constraints = [
        (lambda house, a, b: house[a] == b[0] if house[a] is not None and house[b[1]] is not None else True, (0, 1)),
        (lambda house: house[0] == 'Arnold' if house[0] is not None else (house[2] != 'stew' if house[2] is not None else True), (0, 2)),
        (lambda house: house[2] == 'stir fry' if house[2] is not None else (house[1] != 'colonial' if house[1] is not None else True), (2, 1)),
        (lambda house: house[4] == 'average' if house[4] is not None else (house[2] != 'stir fry' if house[2] is not None else True), (4, 2)),
        (lambda house: house[3] == 'beach' if house[3] is not None else (house[1] != 'ranch' if house[1] is not None else True), (3, 1)),
        (lambda house: house[3] == 'mountain' if house[3] is not None else (house[5] != 'yellow monster' if house[5] is not None else True), (3, 5)),
        (lambda house: house[3] == 'mountain' if house[3] is not None else (house[4] != 'very tall' if house[4] is not None else True), (3, 4)),
        (lambda house: house[2] == 'spaghetti' if house[2] is not None else (house[1] != 'victorian' if house[1] is not None else True), (2, 1)),
        (lambda house: house[4] == 'tall' if house[4] is not None else (house[3] != 'beach' if house[3] is not None else True), (4, 3)),
        (lambda house: house[1] == 'ranch' if house[1] is not None else (house[5] != 'blue master' if house[5] is not None else True), (1, 5)),
        (lambda house: house[3] == 'cultural' if house[3] is not None else (house[2] != 'pizza' if house[2] is not None else True), (3, 2))
    ]
    
    binary_constraints = [
        (5, (lambda a, i, j: (a[i][4] == 'average' and a[j][0] == 'Peter') or (a[i][0] == 'Peter' and a[j][4] == 'average'), [4, 0], 2),
        (10, (lambda a, i, j: (a[i][1] == 'colonial' and a[j][3] == 'camping') or (a[i][3] == 'camping' and a[j][1] == 'colonial'), [1, 3], 2),
        (13, (lambda a, i, j: (a[i][3] == 'mountain' and a[j][5] == 'dunhill') or (a[i][5] == 'dunhill' and a[j][3] == 'mountain'), [3, 5], 1),
        (16, (lambda a, i, j: a[i][4] == 'tall' and a[j][1] == 'victorian' and i < j, [4, 1], None),
        (17, (lambda a, i, j: a[i][2] == 'stir fry' and a[j][0] == 'Bob' and i == j-1, [2, 0], None),
        (18, (lambda a, i: a[i][1] == 'modern' and i < 4, [1], None),
        (19, (lambda a, i, j: a[i][1] == 'craftsman' and a[j][4] == 'short' and i < j, [1, 4], None),
        (20, (lambda a, i, j: a[i][2] == 'stir fry' and a[j][5] == 'prince' and i < j, [2, 5], None),
        (21, (lambda a, i, j: (a[i][2] == 'grilled cheese' and a[j][4] == 'super tall') or (a[i][4] == 'super tall' and a[j][2] == 'grilled cheese'), [2, 4], 3),
        (23, (lambda a, i, j: a[i][5] == 'blends' and a[j][5] == 'blue master' and i == j-1, [5, 5], None),
        (25, (lambda a, i, j: a[i][2] == 'pizza' and a[j][3] == 'cruise' and i < j, [2, 3], None)
    ]
    
    def is_assignment_complete():
        for i in range(6):
            for j in range(len(attributes)):
                if assignment[i][j] is None:
                    return False
        return True
    
    def get_unassigned_variable():
        min_remaining = float('inf')
        best_var = None
        for i in range(6):
            for j in range(len(attributes)):
                if assignment[i][j] is None:
                    if len(var_domains[i][j]) < min_remaining:
                        min_remaining = len(var_domains[i][j])
                        best_var = (i, j)
        return best_var
    
    def forward_check(i, j, value, var_domains):
        new_domains = copy.deepcopy(var_domains)
        for jj in range(len(attributes)):
            if jj != j and assignment[i][jj] is None:
                if value in new_domains[i][jj]:
                    new_domains[i][jj].remove(value)
        for ii in range(6):
            if ii != i and assignment[ii][j] is None:
                if value in new_domains[ii][j]:
                    new_domains[ii][j].remove(value)
        return new_domains
    
    def check_unary_constraints(house_idx):
        house = assignment[house_idx]
        for constraint in unary_constraints:
            if not constraint[0](house):
                return False
        return True
    
    def check_binary_constraints():
        for cid, constraint_func, attrs, dist in binary_constraints:
            if dist is not None:
                for i in range(6):
                    for j in range(6):
                        if i != j and abs(i - j) == dist:
                            if assignment[i][attrs[0]] is not None and assignment[j][attrs[1]] is not None:
                                if not constraint_func(assignment, i, j):
                                    return False
            else:
                if attrs[0] == attrs[1]:
                    for i in range(6):
                        if assignment[i][attrs[0]] is not None:
                            if not constraint_func(assignment, i, i):
                                return False
                    for i in range(5):
                        j = i + 1
                        if assignment[i][attrs[0]] is not None and assignment[j][attrs[1]] is not None:
                            if not constraint_func(assignment, i, j):
                                return False
                else:
                    for i in range(6):
                        for j in range(6):
                            if i != j and assignment[i][attrs[0]] is not None and assignment[j][attrs[1]] is not None:
                                if not constraint_func(assignment, i, j):
                                    return False
        return True
    
    def backtrack():
        if is_assignment_complete():
            return assignment
        var = get_unassigned_variable()
        if var is None:
            return None
        i, j = var
        for value in var_domains[i][j]:
            assignment[i][j] = value
            new_domains = forward_check(i, j, value, var_domains)
            old_domains = var_domains
            var_domains = new_domains
            if not check_unary_constraints(i):
                assignment[i][j] = None
                var_domains = old_domains
                continue
            if not check_binary_constraints():
                assignment[i][j] = None
                var_domains = old_domains
                continue
            result = backtrack()
            if result is not None:
                return result
            assignment[i][j] = None
            var_domains = old_domains
        return None
    
    sol = backtrack()
    
    if sol is None:
        print("No solution found")
        return
    
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
            "rows": []
        }
    }
    
    for i in range(6):
        row = [str(i+1)] + sol[i]
        output["solution"]["rows"].append(row)
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()