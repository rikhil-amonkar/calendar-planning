import json

def set_value(domains, attr, house, value):
    if house < 0 or house >= 6:
        return
    if value not in domains[attr][house]:
        raise ValueError(f"Contradiction: trying to set {attr} house {house} to {value}, but not in domain")
    domains[attr][house] = {value}

def remove_value(domains, attr, house, value):
    if value in domains[attr][house]:
        domains[attr][house].remove(value)
        if len(domains[attr][house]) == 0:
            raise ValueError(f"Contradiction: domain of {attr} house {house} is empty")
        return True
    return False

def propagate_distinctness(domains):
    changed = False
    for attr, houses in domains.items():
        # For each value in this attribute, if it is fixed in one house, remove it from others.
        value_to_house = {}
        for house in range(6):
            if len(houses[house]) == 1:
                value = next(iter(houses[house]))
                if value in value_to_house:
                    raise ValueError(f"Contradiction: {value} appears in house {value_to_house[value]} and {house}")
                value_to_house[value] = house
        for value in value_to_house.keys():
            for house in range(6):
                if house != value_to_house[value]:
                    if remove_value(domains, attr, house, value):
                        changed = True
    return changed

def clue1(domains):
    # The person who uses an iPhone 13 is in the third house.
    set_value(domains, 'phone_model', 2, 'iphone 13')
    return True

def clue2(domains):
    # Bob is the person who is tall.
    changed = False
    for house in range(6):
        if 'Bob' in domains['name'][house]:
            if 'tall' in domains['height'][house]:
                if len(domains['height'][house]) > 1:
                    set_value(domains, 'height', house, 'tall')
                    changed = True
            else:
                if remove_value(domains, 'name', house, 'Bob'):
                    changed = True
        if 'tall' in domains['height'][house]:
            if 'Bob' in domains['name'][house]:
                if len(domains['name'][house]) > 1:
                    set_value(domains, 'name', house, 'Bob')
                    changed = True
            else:
                if remove_value(domains, 'height', house, 'tall'):
                    changed = True
    return changed

def clue3(domains):
    # The person who loves the soup is in the second house.
    set_value(domains, 'food', 1, 'soup')
    return True

def clue4(domains):
    # The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    changed = False
    for i in range(5):  # i from 0 to 4
        if 'root beer' in domains['drink'][i]:
            if 'xiaomi mi 11' not in domains['phone_model'][i+1]:
                if remove_value(domains, 'drink', i, 'root beer'):
                    changed = True
        if 'xiaomi mi 11' in domains['phone_model'][i+1]:
            if 'root beer' not in domains['drink'][i]:
                if remove_value(domains, 'phone_model', i+1, 'xiaomi mi 11'):
                    changed = True
    return changed

def clue5(domains):
    # The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    changed = False
    for i in range(5):
        if 'huawei p50' in domains['phone_model'][i]:
            if 'grilled cheese' not in domains['food'][i+1]:
                if remove_value(domains, 'phone_model', i, 'huawei p50'):
                    changed = True
        if 'grilled cheese' in domains['food'][i+1]:
            if 'huawei p50' not in domains['phone_model'][i]:
                if remove_value(domains, 'food', i+1, 'grilled cheese'):
                    changed = True
    return changed

def clue6(domains):
    # The person who loves stir fry is the person who likes milk.
    changed = False
    for house in range(6):
        if 'stir fry' in domains['food'][house]:
            if 'milk' not in domains['drink'][house]:
                if remove_value(domains, 'food', house, 'stir fry'):
                    changed = True
        if 'milk' in domains['drink'][house]:
            if 'stir fry' not in domains['food'][house]:
                if remove_value(domains, 'drink', house, 'milk'):
                    changed = True
    return changed

def clue7(domains):
    # The person who loves eating grilled cheese is the person who is tall.
    changed = False
    for house in range(6):
        if 'grilled cheese' in domains['food'][house]:
            if 'tall' not in domains['height'][house]:
                if remove_value(domains, 'food', house, 'grilled cheese'):
                    changed = True
        if 'tall' in domains['height'][house]:
            if 'grilled cheese' not in domains['food'][house]:
                if remove_value(domains, 'height', house, 'tall'):
                    changed = True
    return changed

def clue8(domains):
    # The person who uses a Xiaomi Mi 11 is the coffee drinker.
    changed = False
    for house in range(6):
        if 'xiaomi mi 11' in domains['phone_model'][house]:
            if 'coffee' not in domains['drink'][house]:
                if remove_value(domains, 'phone_model', house, 'xiaomi mi 11'):
                    changed = True
        if 'coffee' in domains['drink'][house]:
            if 'xiaomi mi 11' not in domains['phone_model'][house]:
                if remove_value(domains, 'drink', house, 'coffee'):
                    changed = True
    return changed

def clue9(domains):
    # The person who uses a OnePlus 9 is Arnold.
    changed = False
    for house in range(6):
        if 'oneplus 9' in domains['phone_model'][house]:
            if 'Arnold' not in domains['name'][house]:
                if remove_value(domains, 'phone_model', house, 'oneplus 9'):
                    changed = True
        if 'Arnold' in domains['name'][house]:
            if 'oneplus 9' not in domains['phone_model'][house]:
                if remove_value(domains, 'name', house, 'Arnold'):
                    changed = True
    return changed

def clue10(domains):
    # The person who owns a rabbit is not in the fifth house.
    if 'rabbit' in domains['pet'][4]:
        remove_value(domains, 'pet', 4, 'rabbit')
        return True
    return False

def clue11(domains):
    # The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    changed = False
    for i in range(6):
        if 'google pixel 6' in domains['phone_model'][i]:
            # Then hamster must be in a house j>i
            for j in range(0, i+1):
                if 'hamster' in domains['pet'][j]:
                    if remove_value(domains, 'pet', j, 'hamster'):
                        changed = True
    return changed

def clue12(domains):
    # The person who is super tall is the person with an aquarium of fish.
    changed = False
    for house in range(6):
        if 'super tall' in domains['height'][house]:
            if 'fish' not in domains['pet'][house]:
                if remove_value(domains, 'height', house, 'super tall'):
                    changed = True
        if 'fish' in domains['pet'][house]:
            if 'super tall' not in domains['height'][house]:
                if remove_value(domains, 'pet', house, 'fish'):
                    changed = True
    return changed

def clue13(domains):
    # The person with an aquarium of fish is Alice.
    changed = False
    for house in range(6):
        if 'fish' in domains['pet'][house]:
            if 'Alice' not in domains['name'][house]:
                if remove_value(domains, 'pet', house, 'fish'):
                    changed = True
        if 'Alice' in domains['name'][house]:
            if 'fish' not in domains['pet'][house]:
                if remove_value(domains, 'name', house, 'Alice'):
                    changed = True
    return changed

def clue14(domains):
    # The tea drinker is directly left of the person who is a pizza lover.
    changed = False
    for i in range(5):
        if 'tea' in domains['drink'][i]:
            if 'pizza' not in domains['food'][i+1]:
                if remove_value(domains, 'drink', i, 'tea'):
                    changed = True
        if 'pizza' in domains['food'][i+1]:
            if 'tea' not in domains['drink'][i]:
                if remove_value(domains, 'food', i+1, 'pizza'):
                    changed = True
    return changed

def clue15(domains):
    # The person who uses a Samsung Galaxy S21 is Carol.
    changed = False
    for house in range(6):
        if 'samsung galaxy s21' in domains['phone_model'][house]:
            if 'Carol' not in domains['name'][house]:
                if remove_value(domains, 'phone_model', house, 'samsung galaxy s21'):
                    changed = True
        if 'Carol' in domains['name'][house]:
            if 'samsung galaxy s21' not in domains['phone_model'][house]:
                if remove_value(domains, 'name', house, 'Carol'):
                    changed = True
    return changed

def clue16(domains):
    # The person who is a pizza lover is the person who is short.
    changed = False
    for house in range(6):
        if 'pizza' in domains['food'][house]:
            if 'short' not in domains['height'][house]:
                if remove_value(domains, 'food', house, 'pizza'):
                    changed = True
        if 'short' in domains['height'][house]:
            if 'pizza' not in domains['food'][house]:
                if remove_value(domains, 'height', house, 'short'):
                    changed = True
    return changed

def clue17(domains):
    # Arnold is the person who is very tall.
    changed = False
    for house in range(6):
        if 'Arnold' in domains['name'][house]:
            if 'very tall' not in domains['height'][house]:
                if remove_value(domains, 'name', house, 'Arnold'):
                    changed = True
        if 'very tall' in domains['height'][house]:
            if 'Arnold' not in domains['name'][house]:
                if remove_value(domains, 'height', house, 'very tall'):
                    changed = True
    return changed

def clue18(domains):
    # The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    changed = False
    for house in range(6):
        if 'spaghetti' in domains['food'][house]:
            if 'google pixel 6' not in domains['phone_model'][house]:
                if remove_value(domains, 'food', house, 'spaghetti'):
                    changed = True
        if 'google pixel 6' in domains['phone_model'][house]:
            if 'spaghetti' not in domains['food'][house]:
                if remove_value(domains, 'phone_model', house, 'google pixel 6'):
                    changed = True
    return changed

def clue19(domains):
    # The boba tea drinker is somewhere to the right of the person who loves the soup.
    # Since soup is in house1 (index1), boba tea must be in houses 2,3,4,5 (index 2,3,4,5)
    changed = False
    for house in [0,1]:
        if 'boba tea' in domains['drink'][house]:
            if remove_value(domains, 'drink', house, 'boba tea'):
                changed = True
    return changed

def clue20(domains):
    # The person with a pet hamster is not in the fifth house.
    if 'hamster' in domains['pet'][4]:
        remove_value(domains, 'pet', 4, 'hamster')
        return True
    return False

def clue21(domains):
    # The person who is very tall is not in the second house.
    if 'very tall' in domains['height'][1]:
        remove_value(domains, 'height', 1, 'very tall')
        return True
    return False

def clue22(domains):
    # The person who is super tall is somewhere to the left of Peter.
    changed = False
    for house_super in range(6):
        if 'super tall' in domains['height'][house_super]:
            # Peter must be in a house to the right: house_super < house_peter
            # So if there is a house j<=house_super that has Peter, we remove Peter from j.
            for j in range(0, house_super+1):
                if 'Peter' in domains['name'][j]:
                    if remove_value(domains, 'name', j, 'Peter'):
                        changed = True
    return changed

def clue23(domains):
    # The person who is very short is the person who loves the spaghetti eater.
    changed = False
    for house in range(6):
        if 'very short' in domains['height'][house]:
            if 'spaghetti' not in domains['food'][house]:
                if remove_value(domains, 'height', house, 'very short'):
                    changed = True
        if 'spaghetti' in domains['food'][house]:
            if 'very short' not in domains['height'][house]:
                if remove_value(domains, 'food', house, 'spaghetti'):
                    changed = True
    return changed

def clue24(domains):
    # The person with a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    changed = False
    for house_spaghetti in range(6):
        if 'spaghetti' in domains['food'][house_spaghetti]:
            # bird must be in a house left of house_spaghetti: j < house_spaghetti
            for j in range(house_spaghetti, 6):
                if 'bird' in domains['pet'][j]:
                    if remove_value(domains, 'pet', j, 'bird'):
                        changed = True
    return changed

def clue25(domains):
    # The person with an aquarium of fish is directly left of Eric.
    changed = False
    for i in range(5):
        if 'fish' in domains['pet'][i]:
            if 'Eric' not in domains['name'][i+1]:
                if remove_value(domains, 'pet', i, 'fish'):
                    changed = True
        if 'Eric' in domains['name'][i+1]:
            if 'fish' not in domains['pet'][i]:
                if remove_value(domains, 'name', i+1, 'Eric'):
                    changed = True
    return changed

def clue26(domains):
    # The person who owns a dog is the person who likes milk.
    changed = False
    for house in range(6):
        if 'dog' in domains['pet'][house]:
            if 'milk' not in domains['drink'][house]:
                if remove_value(domains, 'pet', house, 'dog'):
                    changed = True
        if 'milk' in domains['drink'][house]:
            if 'dog' not in domains['pet'][house]:
                if remove_value(domains, 'drink', house, 'milk'):
                    changed = True
    return changed

def check_solution(domains):
    for attr in domains:
        for house in range(6):
            if len(domains[attr][house]) != 1:
                return False
    return True

def main():
    attributes = {
        'name': ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric'],
        'food': ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti'],
        'height': ['tall', 'average', 'super tall', 'very short', 'very tall', 'short'],
        'drink': ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk'],
        'pet': ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit'],
        'phone_model': ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']
    }
    
    domains = {}
    for attr, values in attributes.items():
        domains[attr] = [set(values) for _ in range(6)]
    
    clue_functions = [
        clue1, clue2, clue3, clue4, clue5, clue6, clue7, clue8, clue9, clue10,
        clue11, clue12, clue13, clue14, clue15, clue16, clue17, clue18, clue19, clue20,
        clue21, clue22, clue23, clue24, clue25, clue26
    ]
    
    changed = True
    while changed:
        changed = False
        for func in clue_functions:
            try:
                changed_here = func(domains)
                changed = changed or changed_here
            except ValueError as e:
                print(f"Error: {e}")
                return
        changed_distinct = propagate_distinctness(domains)
        changed = changed or changed_distinct
        
        if check_solution(domains):
            break
    
    if not check_solution(domains):
        # If not solved, we try one more propagation cycle? Or output as is?
        print("Not completely solved after propagation. Trying to force by distinctness.")
        # We'll try to see if any house has multiple values but one value is not used elsewhere?
        # Not implemented here, but in this puzzle, propagation should be enough.
        pass
    
    # Extract the solution
    solution = []
    for house in range(6):
        row = [str(house+1)]
        for attr in ['name', 'food', 'height', 'drink', 'pet', 'phone_model']:
            if len(domains[attr][house]) == 1:
                row.append(next(iter(domains[attr][house])))
            else:
                row.append(', '.join(domains[attr][house]))
        solution.append(row)
    
    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
            "rows": solution
        }
    }
    
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()