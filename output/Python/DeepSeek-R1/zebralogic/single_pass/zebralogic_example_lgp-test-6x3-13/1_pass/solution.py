import itertools
import json

def main():
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    
    house_count = 6
    solution_found = None

    for name_perm in itertools.permutations(names):
        if name_perm[2] != 'Eric':
            continue
            
        for occ_perm in itertools.permutations(occupations):
            if occ_perm[0] != 'doctor':
                continue
                
            for gen_perm in itertools.permutations(genres):
                assignment = []
                for i in range(house_count):
                    assignment.append({
                        'name': name_perm[i],
                        'occupation': occ_perm[i],
                        'genre': gen_perm[i]
                    })
                
                if not check_constraints(assignment):
                    continue
                    
                solution_found = assignment
                break
            if solution_found:
                break
        if solution_found:
            break
            
    if solution_found is None:
        print('{"solution": {}}')
        return

    output = {
        "solution": {
            "header": ["House", "Name", "favorite book genre", "occupation"],
            "rows": []
        }
    }
    
    for i in range(house_count):
        house_data = solution_found[i]
        output["solution"]["rows"].append([
            str(i+1),
            house_data['name'],
            house_data['genre'],
            house_data['occupation']
        ])
        
    print(json.dumps(output, indent=2))

def check_constraints(assign):
    houses = assign

    def house_of_attr_value(attr, value):
        for i, house in enumerate(houses):
            if house[attr] == value:
                return i
        return -1

    def left_of(i, j):
        return i < j

    def adjacent(i, j):
        return abs(i - j) == 1

    name_index = {house['name']: i for i, house in enumerate(houses)}
    genre_index = {house['genre']: i for i, house in enumerate(houses)}
    occ_index = {house['occupation']: i for i, house in enumerate(houses)}

    if houses[house_of_attr_value('name', 'Alice')]['genre'] != 'fantasy':
        return False

    carol_index = name_index['Carol']
    if houses[carol_index]['genre'] != 'mystery':
        return False

    mystery_index = genre_index['mystery']
    if not adjacent(mystery_index, name_index['Bob']):
        return False

    if houses[house_of_attr_value('occupation', 'lawyer')]['genre'] != 'fantasy':
        return False

    if name_index['Bob'] == 4:
        return False

    arnold_index = name_index['Arnold']
    engineer_index = occ_index['engineer']
    if not left_of(arnold_index, engineer_index):
        return False

    alice_index = name_index['Alice']
    if alice_index == 0:
        return False
    if houses[alice_index - 1]['occupation'] != 'nurse':
        return False

    if houses[house_of_attr_value('genre', 'biography')]['occupation'] != 'teacher':
        return False

    histfic_index = genre_index['historical fiction']
    teacher_index = occ_index['teacher']
    if not left_of(histfic_index, teacher_index):
        return False

    if houses[0]['occupation'] != 'doctor':
        return False

    if houses[house_of_attr_value('genre', 'science fiction')]['occupation'] != 'artist':
        return False

    if name_index['Eric'] != 2:
        return False

    if genre_index['mystery'] == 4:
        return False

    return True

if __name__ == '__main__':
    main()