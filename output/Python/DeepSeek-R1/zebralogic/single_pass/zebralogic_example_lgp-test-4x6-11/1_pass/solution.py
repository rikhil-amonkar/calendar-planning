import itertools
import json

def main():
    attributes = {
        'Hobby': ['cooking', 'painting', 'gardening', 'photography'],
        'MusicGenre': ['pop', 'rock', 'classical', 'jazz'],
        'BookGenre': ['fantasy', 'mystery', 'romance', 'science fiction'],
        'Birthday': ['april', 'jan', 'sept', 'feb'],
        'Name': ['Peter', 'Alice', 'Eric', 'Arnold'],
        'Animal': ['horse', 'fish', 'cat', 'bird']
    }
    
    attribute_order = ['Hobby', 'MusicGenre', 'BookGenre', 'Birthday', 'Name', 'Animal']
    
    # Define constraints as functions
    def clue1(a):
        return a['Hobby']['cooking'] == a['BookGenre']['romance']
    
    def clue2(a):
        return a['Birthday']['feb'] == a['MusicGenre']['pop']
    
    def clue3(a):
        return a['Name']['Eric'] != 1
    
    def clue4(a):
        return a['BookGenre']['romance'] != 3
    
    def clue5(a):
        return a['Birthday']['feb'] == a['Animal']['fish']
    
    def clue6(a):
        return a['Name']['Alice'] > a['BookGenre']['fantasy']
    
    def clue7(a):
        return a['Animal']['horse'] == a['MusicGenre']['rock']
    
    def clue8(a):
        return a['Hobby']['gardening'] == a['Birthday']['april']
    
    def clue9(a):
        return a['MusicGenre']['jazz'] == a['Hobby']['cooking']
    
    def clue10(a):
        return a['MusicGenre']['rock'] == a['BookGenre']['mystery']
    
    def clue11(a):
        painting_pos = a['Hobby']['painting']
        romance_pos = a['BookGenre']['romance']
        return painting_pos + 1 == romance_pos
    
    def clue12(a):
        return a['Name']['Peter'] == a['MusicGenre']['pop']
    
    def clue13(a):
        return a['Hobby']['gardening'] == a['Name']['Arnold']
    
    def clue14(a):
        rock_pos = a['MusicGenre']['rock']
        jan_pos = a['Birthday']['jan']
        return rock_pos + 1 == jan_pos
    
    def clue15(a):
        return a['Hobby']['cooking'] != 2
    
    def clue16(a):
        return a['Animal']['cat'] > a['Animal']['horse']
    
    constraints = [
        (clue1, ['Hobby', 'BookGenre']),
        (clue2, ['Birthday', 'MusicGenre']),
        (clue3, ['Name']),
        (clue4, ['BookGenre']),
        (clue5, ['Birthday', 'Animal']),
        (clue6, ['Name', 'BookGenre']),
        (clue7, ['Animal', 'MusicGenre']),
        (clue8, ['Hobby', 'Birthday']),
        (clue9, ['Hobby', 'MusicGenre']),
        (clue10, ['MusicGenre', 'BookGenre']),
        (clue11, ['Hobby', 'BookGenre']),
        (clue12, ['Name', 'MusicGenre']),
        (clue13, ['Hobby', 'Name']),
        (clue14, ['MusicGenre', 'Birthday']),
        (clue15, ['Hobby']),
        (clue16, ['Animal'])
    ]
    
    attribute_constraints = {attr: [] for attr in attribute_order}
    for constr_func, req_attrs in constraints:
        for attr in req_attrs:
            if attr in attribute_constraints:
                attribute_constraints[attr].append((constr_func, req_attrs))
    
    def backtrack(assignments, remaining_attrs):
        if not remaining_attrs:
            return assignments
        
        next_attr = remaining_attrs[0]
        domain = attributes[next_attr]
        for perm in itertools.permutations(domain):
            mapping = {}
            for idx, value in enumerate(perm):
                mapping[value] = idx
            
            new_assignments = assignments.copy()
            new_assignments[next_attr] = mapping
            
            to_check = attribute_constraints[next_attr]
            valid = True
            for (func, req_attrs) in to_check:
                if all(attr in new_assignments for attr in req_attrs):
                    if not func(new_assignments):
                        valid = False
                        break
            
            if not valid:
                continue
            
            result = backtrack(new_assignments, remaining_attrs[1:])
            if result is not None:
                return result
        
        return None
    
    initial_assignments = {}
    solution_assignments = backtrack(initial_assignments, attribute_order)
    
    if solution_assignments is None:
        print(json.dumps({"solution": {"header": [], "rows": []}}))
        return
    
    house_attributes = ['Name', 'Hobby', 'Animal', 'BookGenre', 'Birthday', 'MusicGenre']
    rows = []
    for house_index in range(4):
        row = [str(house_index + 1)]
        for attr in house_attributes:
            mapping = solution_assignments[attr]
            arr = [None] * 4
            for value, idx in mapping.items():
                arr[idx] = value
            row.append(arr[house_index])
        rows.append(row)
    
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == '__main__':
    main()