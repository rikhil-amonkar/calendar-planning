import json

def main():
    houses = [
        {'name': 'Peter', 'music': None, 'child': None, 'book': None},
        {'name': None, 'music': None, 'child': None, 'book': None},
        {'name': None, 'music': None, 'child': None, 'book': None}
    ]
    
    solution_found = False
    for m_idx in [1, 2]:
        h = [
            {'name': 'Peter', 'music': None, 'child': None, 'book': None},
            {'name': None, 'music': None, 'child': None, 'book': None},
            {'name': None, 'music': None, 'child': None, 'book': None}
        ]
        
        h[m_idx]['book'] = 'mystery'
        h[m_idx]['name'] = 'Eric'
        h[m_idx]['music'] = 'classical'
        
        left_idx = m_idx - 1
        h[left_idx]['child'] = 'Fred'
        
        candidates = [0, 1, 2]
        candidates.remove(m_idx)
        candidates.remove(left_idx)
        other_idx = candidates[0]
        
        h[other_idx]['book'] = 'science fiction'
        h[other_idx]['child'] = 'Meredith'
        
        h[left_idx]['book'] = 'romance'
        
        h[m_idx]['child'] = 'Bella'
        
        remaining_name_house = [i for i in [0, 1, 2] if i != 0 and i != m_idx]
        if remaining_name_house:
            h[remaining_name_house[0]]['name'] = 'Arnold'
        
        non_mystery_indices = [i for i in [0, 1, 2] if i != m_idx]
        perms = [('pop', 'rock'), ('rock', 'pop')]
        found_music = False
        for perm in perms:
            h[non_mystery_indices[0]]['music'] = perm[0]
            h[non_mystery_indices[1]]['music'] = perm[1]
            
            romance_idx = left_idx
            rock_idx = None
            for i in range(3):
                if h[i]['music'] == 'rock':
                    rock_idx = i
                    break
            
            if rock_idx is not None and rock_idx > romance_idx:
                found_music = True
                break
        
        if found_music:
            houses = h
            solution_found = True
            break
    
    if not solution_found:
        print(json.dumps({"error": "No solution found"}))
        return
    
    rows = []
    for i in range(3):
        row = [
            str(i+1),
            houses[i]['name'],
            houses[i]['music'],
            houses[i]['child'],
            houses[i]['book']
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == '__main__':
    main()