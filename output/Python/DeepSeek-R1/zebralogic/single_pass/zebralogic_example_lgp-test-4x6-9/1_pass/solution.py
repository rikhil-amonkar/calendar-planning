import json

def main():
    houses = [1, 2, 3, 4]
    categories = ['Name', 'Flower', 'Height', 'Mother', 'Occupation', 'FavoriteSport']
    
    possible_values = {
        'Name': ['Peter', 'Arnold', 'Eric', 'Alice'],
        'Flower': ['daffodils', 'carnations', 'roses', 'lilies'],
        'Height': ['very short', 'short', 'tall', 'average'],
        'Mother': ['Janelle', 'Kailyn', 'Holly', 'Aniya'],
        'Occupation': ['engineer', 'doctor', 'teacher', 'artist'],
        'FavoriteSport': ['swimming', 'basketball', 'tennis', 'soccer']
    }
    
    possibilities = {}
    for cat in categories:
        possibilities[cat] = {}
        for house in houses:
            possibilities[cat][house] = set(possible_values[cat])
    
    # Apply initial direct assignments
    possibilities['Occupation'][1] = {'teacher'}
    for house in [2, 3, 4]:
        possibilities['Occupation'][house].discard('teacher')
    
    possibilities['Name'][3].discard('Arnold')
    
    same_house_constraints = [
        (('FavoriteSport', 'swimming'), ('Flower', 'roses')),
        (('Name', 'Eric'), ('Flower', 'roses')),
        (('Name', 'Arnold'), ('Height', 'tall')),
        (('FavoriteSport', 'soccer'), ('Height', 'short')),
        (('Mother', 'Janelle'), ('Flower', 'carnations')),
        (('FavoriteSport', 'basketball'), ('Height', 'average')),
        (('Name', 'Peter'), ('Occupation', 'doctor')),
        (('Mother', 'Aniya'), ('Name', 'Alice')),
        (('Name', 'Arnold'), ('Flower', 'lilies'))
    ]
    
    relative_constraints = [
        (('Flower', 'daffodils'), ('Occupation', 'engineer'), 'right'),
        (('Mother', 'Holly'), ('Height', 'average'), 'right')
    ]
    
    changed = True
    while changed:
        changed = False
        
        for con in same_house_constraints:
            (cat1, val1), (cat2, val2) = con
            H1 = set()
            for h in houses:
                if val1 in possibilities[cat1][h]:
                    H1.add(h)
            H2 = set()
            for h in houses:
                if val2 in possibilities[cat2][h]:
                    H2.add(h)
            H = H1 & H2
            for h in houses:
                if h not in H and val1 in possibilities[cat1][h]:
                    possibilities[cat1][h].remove(val1)
                    changed = True
            for h in houses:
                if h not in H and val2 in possibilities[cat2][h]:
                    possibilities[cat2][h].remove(val2)
                    changed = True
        
        for con in relative_constraints:
            (catA, valA), (catB, valB), rel = con
            if rel != 'right':
                continue
            HA = set()
            for h in houses:
                if valA in possibilities[catA][h]:
                    HA.add(h)
            HB = set()
            for h in houses:
                if valB in possibilities[catB][h]:
                    HB.add(h)
            new_HA = set()
            for hA in HA:
                if any(hB < hA for hB in HB):
                    new_HA.add(hA)
            new_HB = set()
            for hB in HB:
                if any(hA > hB for hA in HA):
                    new_HB.add(hB)
            for h in houses:
                if h not in new_HA and valA in possibilities[catA][h]:
                    possibilities[catA][h].remove(valA)
                    changed = True
            for h in houses:
                if h not in new_HB and valB in possibilities[catB][h]:
                    possibilities[catB][h].remove(valB)
                    changed = True
        
        for cat in categories:
            for house in houses:
                if len(possibilities[cat][house]) == 1:
                    val = next(iter(possibilities[cat][house]))
                    for other_house in houses:
                        if other_house != house and val in possibilities[cat][other_house]:
                            possibilities[cat][other_house].remove(val)
                            changed = True
        
        for cat in categories:
            for value in possible_values[cat]:
                count = 0
                last_house = None
                for house in houses:
                    if value in possibilities[cat][house]:
                        count += 1
                        last_house = house
                if count == 1 and last_house is not None:
                    if possibilities[cat][last_house] != {value}:
                        possibilities[cat][last_house] = {value}
                        changed = True
    
    header = ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"]
    rows = []
    for house in sorted(houses):
        row = [str(house)]
        for cat in header[1:]:
            if len(possibilities[cat][house]) == 1:
                row.append(next(iter(possibilities[cat][house])))
            else:
                raise RuntimeError(f"House {house} has multiple possibilities for {cat}: {possibilities[cat][house]}")
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution_dict, indent=2))

if __name__ == "__main__":
    main()