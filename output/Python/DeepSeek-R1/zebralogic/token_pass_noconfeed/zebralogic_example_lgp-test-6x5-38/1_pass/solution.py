import json
from copy import deepcopy

def main():
    attributes = ['Name', 'Birthday', 'Food', 'Height', 'CarModel']
    all_values = {
        'Name': ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter'],
        'Birthday': ['jan', 'feb', 'mar', 'april', 'may', 'sept'],
        'Food': ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza'],
        'Height': ['very short', 'short', 'average', 'tall', 'very tall', 'super tall'],
        'CarModel': ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']
    }
    
    domains = {}
    for attr in attributes:
        domains[attr] = [set(all_values[attr]) for _ in range(6)]
    
    def assign(attr, house, value):
        if house < 0 or house >= 6:
            return
        domains[attr][house] = {value}
        for i in range(6):
            if i != house:
                domains[attr][i].discard(value)
    
    def enforce_uniqueness(domains):
        for attr in attributes:
            value_counts = {value: [] for value in all_values[attr]}
            for house in range(6):
                for value in domains[attr][house]:
                    value_counts[value].append(house)
            for value, houses in value_counts.items():
                if len(houses) == 1:
                    house = houses[0]
                    if value in domains[attr][house] and len(domains[attr][house]) > 1:
                        domains[attr][house] = {value}
    
    def reduce_domains(domains):
        constraints = [
            clue1, clue2, clue3, clue4, clue5, clue6, clue7, clue8, clue9, clue10,
            clue11, clue12, clue13, clue14, clue15, clue16, clue17, clue18, clue19, clue20,
            clue21, clue22
        ]
        changed = True
        while changed:
            old_domains = deepcopy(domains)
            for constraint in constraints:
                constraint(domains)
            enforce_uniqueness(domains)
            changed = old_domains != domains
        return domains
    
    def clue1(domains):
        for i in range(6):
            if 'honda civic' in domains['CarModel'][i]:
                domains['Height'][i] = domains['Height'][i] & {'short'}
            if 'short' in domains['Height'][i]:
                domains['CarModel'][i] = domains['CarModel'][i] & {'honda civic'}
    
    def clue2(domains):
        assign('CarModel', 4, 'ford f150')
    
    def clue3(domains):
        eric_houses = [i for i in range(6) if 'Eric' in domains['Name'][i]]
        if eric_houses:
            max_eric = max(eric_houses)
            for i in range(max_eric, 6):
                domains['Food'][i].discard('stir fry')
        for i in range(6):
            if 'stir fry' in domains['Food'][i]:
                for j in range(i+1, 6):
                    domains['Name'][j].discard('Eric')
    
    def clue4(domains):
        carol_houses = [i for i in range(6) if 'Carol' in domains['Name'][i]]
        if carol_houses:
            max_carol = max(carol_houses)
            for i in range(max_carol, 6):
                domains['Birthday'][i].discard('may')
        for i in range(6):
            if 'may' in domains['Birthday'][i]:
                for j in range(i+1, 6):
                    domains['Name'][j].discard('Carol')
    
    def clue5(domains):
        april_houses = [i for i in range(6) if 'april' in domains['Birthday'][i]]
        if april_houses:
            min_april = min(april_houses)
            for i in range(min_april, 6):
                domains['Height'][i].discard('very short')
        for i in range(6):
            if 'very short' in domains['Height'][i]:
                for j in range(i+1, 6):
                    domains['Birthday'][j].discard('april')
    
    def clue6(domains):
        domains['CarModel'][2].discard('bmw 3 series')
    
    def clue7(domains):
        for i in range(6):
            if 'stir fry' in domains['Food'][i]:
                if i+3 < 6:
                    domains['Food'][i+3] = domains['Food'][i+3] & {'pizza'}
                if i-3 >= 0:
                    domains['Food'][i-3] = domains['Food'][i-3] & {'pizza'}
            if 'pizza' in domains['Food'][i]:
                if i+3 < 6:
                    domains['Food'][i+3] = domains['Food'][i+3] & {'stir fry'}
                if i-3 >= 0:
                    domains['Food'][i-3] = domains['Food'][i-3] & {'stir fry'}
    
    def clue8(domains):
        for i in range(1, 6):
            if 'Eric' in domains['Name'][i]:
                domains['Food'][i-1] = domains['Food'][i-1] & {'soup'}
        for i in range(5):
            if 'soup' in domains['Food'][i]:
                domains['Name'][i+1] = domains['Name'][i+1] & {'Eric'}
    
    def clue9(domains):
        for i in range(6):
            if 'may' in domains['Birthday'][i]:
                for j in [i-1, i+1]:
                    if 0 <= j < 6:
                        domains['Food'][j] = domains['Food'][j] & {'spaghetti'}
            if 'spaghetti' in domains['Food'][i]:
                for j in [i-1, i+1]:
                    if 0 <= j < 6:
                        domains['Birthday'][j] = domains['Birthday'][j] & {'may'}
    
    def clue10(domains):
        for i in range(1, 6):
            if 'bmw 3 series' in domains['CarModel'][i]:
                domains['Name'][i-1] = domains['Name'][i-1] & {'Alice'}
        for i in range(5):
            if 'Alice' in domains['Name'][i]:
                domains['CarModel'][i+1] = domains['CarModel'][i+1] & {'bmw 3 series'}
    
    def clue11(domains):
        tall_houses = [i for i in range(6) if 'tall' in domains['Height'][i]]
        if tall_houses:
            min_tall = min(tall_houses)
            for i in range(min_tall, 6):
                domains['CarModel'][i].discard('tesla model 3')
        for i in range(6):
            if 'tesla model 3' in domains['CarModel'][i]:
                for j in range(i+1, 6):
                    domains['Height'][j].discard('tall')
    
    def clue12(domains):
        for i in range(6):
            if 'very tall' in domains['Height'][i]:
                domains['CarModel'][i] = domains['CarModel'][i] & {'toyota camry'}
            if 'toyota camry' in domains['CarModel'][i]:
                domains['Height'][i] = domains['Height'][i] & {'very tall'}
    
    def clue13(domains):
        for i in range(1, 6):
            if 'pizza' in domains['Food'][i]:
                domains['Name'][i-1] = domains['Name'][i-1] & {'Peter'}
        for i in range(5):
            if 'Peter' in domains['Name'][i]:
                domains['Food'][i+1] = domains['Food'][i+1] & {'pizza'}
    
    def clue14(domains):
        domains['Food'][2].discard('stew')
    
    def clue15(domains):
        for i in range(6):
            if 'very short' in domains['Height'][i]:
                for j in [i-2, i+2]:
                    if 0 <= j < 6:
                        domains['Birthday'][j] = domains['Birthday'][j] & {'sept'}
            if 'sept' in domains['Birthday'][i]:
                for j in [i-2, i+2]:
                    if 0 <= j < 6:
                        domains['Height'][j] = domains['Height'][j] & {'very short'}
    
    def clue16(domains):
        for i in range(6):
            if 'mar' in domains['Birthday'][i]:
                for j in [i-2, i+2]:
                    if 0 <= j < 6:
                        domains['Height'][j] = domains['Height'][j] & {'super tall'}
            if 'super tall' in domains['Height'][i]:
                for j in [i-2, i+2]:
                    if 0 <= j < 6:
                        domains['Birthday'][j] = domains['Birthday'][j] & {'mar'}
    
    def clue17(domains):
        for i in range(6):
            if 'tall' in domains['Height'][i]:
                domains['Name'][i] = domains['Name'][i] & {'Bob'}
            if 'Bob' in domains['Name'][i]:
                domains['Height'][i] = domains['Height'][i] & {'tall'}
    
    def clue18(domains):
        alice_houses = [i for i in range(6) if 'Alice' in domains['Name'][i]]
        if alice_houses:
            min_alice = min(alice_houses)
            for i in range(0, min_alice+1):
                domains['Birthday'][i].discard('may')
        for i in range(6):
            if 'may' in domains['Birthday'][i]:
                for j in range(0, i):
                    domains['Name'][j].discard('Alice')
    
    def clue19(domains):
        assign('Height', 3, 'very short')
    
    def clue20(domains):
        for i in range(6):
            if 'mar' in domains['Birthday'][i]:
                domains['Height'][i] = domains['Height'][i] & {'short'}
            if 'short' in domains['Height'][i]:
                domains['Birthday'][i] = domains['Birthday'][i] & {'mar'}
    
    def clue21(domains):
        for i in range(6):
            if 'Carol' in domains['Name'][i]:
                domains['CarModel'][i] = domains['CarModel'][i] & {'tesla model 3'}
            if 'tesla model 3' in domains['CarModel'][i]:
                domains['Name'][i] = domains['Name'][i] & {'Carol'}
    
    def clue22(domains):
        for i in range(6):
            if 'Eric' in domains['Name'][i]:
                domains['Birthday'][i] = domains['Birthday'][i] & {'jan'}
            if 'jan' in domains['Birthday'][i]:
                domains['Name'][i] = domains['Name'][i] & {'Eric'}
    
    reduce_domains(domains)
    
    assignment = {}
    for attr in attributes:
        assignment[attr] = [None] * 6
        for i in range(6):
            if len(domains[attr][i]) == 1:
                assignment[attr][i] = next(iter(domains[attr][i]))
    
    rows = []
    for i in range(6):
        row = [str(i+1)]
        for attr in attributes:
            row.append(assignment[attr][i])
        rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))

if __name__ == '__main__':
    main()