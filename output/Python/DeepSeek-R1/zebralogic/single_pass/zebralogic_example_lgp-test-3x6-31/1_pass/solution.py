import itertools
import json

def main():
    attributes = {
        'name': ['Eric', 'Peter', 'Arnold'],
        'drink': ['milk', 'water', 'tea'],
        'vacation': ['mountain', 'city', 'beach'],
        'house_style': ['colonial', 'victorian', 'ranch'],
        'animal': ['cat', 'bird', 'horse'],
        'birthday': ['jan', 'sept', 'april']
    }
    
    def satisfies(houses):
        # Constraint 1: colonial left of milk
        colonial_index = None
        milk_index = None
        for i, house in enumerate(houses):
            if house['house_style'] == 'colonial':
                colonial_index = i
            if house['drink'] == 'milk':
                milk_index = i
        if colonial_index is None or milk_index is None:
            return False
        if colonial_index >= milk_index:
            return False

        # Constraint 2: city directly left of victorian
        found = False
        for i in range(2):
            if houses[i]['vacation'] == 'city' and houses[i+1]['house_style'] == 'victorian':
                found = True
                break
        if not found:
            return False

        # Constraint 3: jan directly left of cat
        found = False
        for i in range(2):
            if houses[i]['birthday'] == 'jan' and houses[i+1]['animal'] == 'cat':
                found = True
                break
        if not found:
            return False

        # Constraint 4: water -> mountain
        for house in houses:
            if house['drink'] == 'water':
                if house['vacation'] != 'mountain':
                    return False
                break
        else:
            return False

        # Constraint 5: horse -> Peter
        for house in houses:
            if house['animal'] == 'horse':
                if house['name'] != 'Peter':
                    return False
                break
        else:
            return False

        # Constraint 6: victorian right of beach
        victorian_index = None
        beach_index = None
        for i, house in enumerate(houses):
            if house['house_style'] == 'victorian':
                victorian_index = i
            if house['vacation'] == 'beach':
                beach_index = i
        if victorian_index is None or beach_index is None:
            return False
        if victorian_index <= beach_index:
            return False

        # Constraint 7: city -> Peter
        for house in houses:
            if house['vacation'] == 'city':
                if house['name'] != 'Peter':
                    return False
                break
        else:
            return False

        # Constraint 8: mountain -> april
        for house in houses:
            if house['vacation'] == 'mountain':
                if house['birthday'] != 'april':
                    return False
                break
        else:
            return False

        # Constraint 9: water -> Eric
        for house in houses:
            if house['drink'] == 'water':
                if house['name'] != 'Eric':
                    return False
                break
        else:
            return False

        return True

    def find_solution():
        for name_perm in itertools.permutations(attributes['name']):
            for drink_perm in itertools.permutations(attributes['drink']):
                for vacation_perm in itertools.permutations(attributes['vacation']):
                    for house_style_perm in itertools.permutations(attributes['house_style']):
                        for animal_perm in itertools.permutations(attributes['animal']):
                            for birthday_perm in itertools.permutations(attributes['birthday']):
                                houses = []
                                for i in range(3):
                                    house = {
                                        'name': name_perm[i],
                                        'drink': drink_perm[i],
                                        'vacation': vacation_perm[i],
                                        'house_style': house_style_perm[i],
                                        'animal': animal_perm[i],
                                        'birthday': birthday_perm[i]
                                    }
                                    houses.append(house)
                                if satisfies(houses):
                                    return houses
        return None

    solution_houses = find_solution()
    
    header = ["House", "Name", "Favorite Drink", "Vacation", "House Style", "Animal", "Birthday"]
    rows = []
    if solution_houses:
        for i, house in enumerate(solution_houses):
            row = [str(i+1), house['name'], house['drink'], house['vacation'], house['house_style'], house['animal'], house['birthday']]
            rows.append(row)
    else:
        rows = []
    
    output_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output_dict))

if __name__ == "__main__":
    main()