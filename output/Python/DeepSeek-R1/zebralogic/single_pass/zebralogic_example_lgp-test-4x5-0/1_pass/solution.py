import json

def main():
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    
    n_houses = 4
    
    def constraint_check(assignment, k):
        houses = assignment
        n = k + 1
        
        for i in range(n):
            # Clue 1: Dragonfruit smoothie lover is Eric
            if houses[i]['smoothie'] == 'dragonfruit':
                if houses[i]['name'] != 'Eric':
                    return False
            if houses[i]['name'] == 'Eric':
                if houses[i]['smoothie'] != 'dragonfruit':
                    return False
                    
            # Clue 2: Dunhill smoker likes Cherry smoothie
            if houses[i]['cigar'] == 'dunhill':
                if houses[i]['smoothie'] != 'cherry':
                    return False
            if houses[i]['smoothie'] == 'cherry':
                if houses[i]['cigar'] != 'dunhill':
                    return False
                    
            # Clue 6: Prince smoker uses OnePlus 9
            if houses[i]['cigar'] == 'prince':
                if houses[i]['phone'] != 'oneplus 9':
                    return False
            if houses[i]['phone'] == 'oneplus 9':
                if houses[i]['cigar'] != 'prince':
                    return False
                    
            # Clue 8: Very short uses iPhone 13
            if houses[i]['height'] == 'very short':
                if houses[i]['phone'] != 'iphone 13':
                    return False
            if houses[i]['phone'] == 'iphone 13':
                if houses[i]['height'] != 'very short':
                    return False
                    
            # Clue 10: Dunhill smoker is short
            if houses[i]['cigar'] == 'dunhill':
                if houses[i]['height'] != 'short':
                    return False
            if houses[i]['height'] == 'short':
                if houses[i]['cigar'] != 'dunhill':
                    return False
                    
            # Clue 12: Arnold uses Google Pixel 6
            if houses[i]['name'] == 'Arnold':
                if houses[i]['phone'] != 'google pixel 6':
                    return False
            if houses[i]['phone'] == 'google pixel 6':
                if houses[i]['name'] != 'Arnold':
                    return False
                    
            # Clue 13: Dragonfruit smoothie lover smokes Pall Mall
            if houses[i]['smoothie'] == 'dragonfruit':
                if houses[i]['cigar'] != 'pall mall':
                    return False
            if houses[i]['cigar'] == 'pall mall':
                if houses[i]['smoothie'] != 'dragonfruit':
                    return False
        
        # Clue 3: Samsung Galaxy S21 directly left of iPhone 13
        for i in range(n-1):
            if houses[i]['phone'] == 'samsung galaxy s21' and houses[i+1]['phone'] != 'iphone 13':
                return False
            if houses[i+1]['phone'] == 'iphone 13' and houses[i]['phone'] != 'samsung galaxy s21':
                return False
        
        # Clue 4: Dunhill smoker is right of very short person
        for i in range(n):
            if houses[i]['cigar'] == 'dunhill':
                found = False
                for j in range(i):
                    if houses[j]['height'] == 'very short':
                        found = True
                        break
                if not found:
                    return False
        if n == 4:
            for i in range(4):
                if houses[i]['height'] == 'very short':
                    found = False
                    for j in range(i+1, 4):
                        if houses[j]['cigar'] == 'dunhill':
                            found = True
                            break
                    if not found:
                        return False
        
        # Clue 5: Watermelon smoothie lover is right of Desert smoothie lover
        for i in range(n):
            if houses[i]['smoothie'] == 'watermelon':
                found = False
                for j in range(i):
                    if houses[j]['smoothie'] == 'desert':
                        found = True
                        break
                if not found:
                    return False
        if n == 4:
            for i in range(4):
                if houses[i]['smoothie'] == 'desert':
                    found = False
                    for j in range(i+1, 4):
                        if houses[j]['smoothie'] == 'watermelon':
                            found = True
                            break
                    if not found:
                        return False
        
        # Clue 7: Tall person is in third house
        if n > 2:
            if houses[2]['height'] != 'tall':
                return False
        
        # Clue 9: Blue Master smoker not in first house
        if n >= 1:
            if houses[0]['cigar'] == 'blue master':
                return False
        
        # Clue 11: Peter not in third house
        if n > 2:
            if houses[2]['name'] == 'Peter':
                return False
        
        return True

    def backtrack(assignment, used, k):
        if k == 4:
            return assignment[:]
        
        available_names = [n for n in names if n not in used['name']]
        available_smoothies = [s for s in smoothies if s not in used['smoothie']]
        available_cigars = [c for c in cigars if c not in used['cigar']]
        available_heights = [h for h in heights if h not in used['height']]
        available_phones = [p for p in phones if p not in used['phone']]
        
        for name in available_names:
            for smoothie in available_smoothies:
                for cigar in available_cigars:
                    for height in available_heights:
                        for phone in available_phones:
                            candidate = {
                                'name': name,
                                'smoothie': smoothie,
                                'cigar': cigar,
                                'height': height,
                                'phone': phone
                            }
                            assignment.append(candidate)
                            used['name'].add(name)
                            used['smoothie'].add(smoothie)
                            used['cigar'].add(cigar)
                            used['height'].add(height)
                            used['phone'].add(phone)
                            
                            if constraint_check(assignment, k):
                                result = backtrack(assignment, used, k+1)
                                if result is not None:
                                    return result
                            
                            assignment.pop()
                            used['name'].remove(name)
                            used['smoothie'].remove(smoothie)
                            used['cigar'].remove(cigar)
                            used['height'].remove(height)
                            used['phone'].remove(phone)
        return None

    used = {
        'name': set(),
        'smoothie': set(),
        'cigar': set(),
        'height': set(),
        'phone': set()
    }
    assignment = []
    sol = backtrack(assignment, used, 0)
    
    if sol is None:
        print('{"solution": {}}')
        return
    
    header = ['House', 'Name', 'Smoothie', 'Cigar', 'Height', 'Phone']
    rows = []
    for i in range(4):
        house = sol[i]
        row = [
            str(i+1),
            house['name'],
            house['smoothie'],
            house['cigar'],
            house['height'],
            house['phone']
        ]
        rows.append(row)
    
    result_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(result_dict))

if __name__ == "__main__":
    main()