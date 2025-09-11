import itertools
import json

def main():
    names = ['Arnold', 'Peter', 'Eric']
    animals = ['bird', 'horse', 'cat']
    birthdays = ['jan', 'sept', 'april']
    hobbies = ['photography', 'cooking', 'gardening']
    drinks = ['milk', 'water', 'tea']
    haircolors = ['black', 'brown', 'blonde']

    # Generate permutations with fixed constraints
    animal_perms = list(itertools.permutations(animals))
    animal_perms = [p for p in animal_perms if p[1] == 'cat']

    birthday_perms = list(itertools.permutations(birthdays))
    birthday_perms = [p for p in birthday_perms if p[2] == 'april']

    name_perms = list(itertools.permutations(names))
    hobby_perms = list(itertools.permutations(hobbies))
    drink_perms = list(itertools.permutations(drinks))
    haircolor_perms = list(itertools.permutations(haircolors))

    def is_valid(name_p, animal_p, birthday_p, hobby_p, drink_p, haircolor_p):
        # Check clue 3: Eric not in first house
        if name_p[0] == 'Eric':
            return False

        # Check clue 5: Blonde left of milk
        blonde_pos = None
        milk_pos = None
        for i in range(3):
            if haircolor_p[i] == 'blonde':
                blonde_pos = i
            if drink_p[i] == 'milk':
                milk_pos = i
        if blonde_pos is not None and milk_pos is not None:
            if not (blonde_pos < milk_pos):
                return False
        else:
            return False

        # Check clue 6: gardening → milk
        for i in range(3):
            if hobby_p[i] == 'gardening' and drink_p[i] != 'milk':
                return False

        # Check clue 7: cat lover has brown hair
        if haircolor_p[1] != 'brown':
            return False

        # Check clue 1: brown hair → cooking
        if hobby_p[1] != 'cooking':
            return False

        # Check clue 8: Arnold's animal is bird
        arnold_index = name_p.index('Arnold')
        if animal_p[arnold_index] != 'bird':
            return False

        # Check clue 9: drink water → photography
        for i in range(3):
            if drink_p[i] == 'water' and hobby_p[i] != 'photography':
                return False

        # Check clue 10: birthday sept is directly left of Arnold
        sept_index = birthday_p.index('sept')
        if sept_index + 1 >= 3 or name_p[sept_index + 1] != 'Arnold':
            return False

        return True

    # Iterate through all combinations
    for name_p in name_perms:
        for animal_p in animal_perms:
            for birthday_p in birthday_perms:
                for hobby_p in hobby_perms:
                    for drink_p in drink_perms:
                        for haircolor_p in haircolor_perms:
                            if is_valid(name_p, animal_p, birthday_p, hobby_p, drink_p, haircolor_p):
                                # Build solution
                                rows = []
                                for i in range(3):
                                    house = str(i + 1)
                                    name = name_p[i]
                                    animal = animal_p[i]
                                    birthday = birthday_p[i]
                                    hobby = hobby_p[i]
                                    drink = drink_p[i]
                                    haircolor = haircolor_p[i]
                                    rows.append([house, name, animal, birthday, hobby, drink, haircolor])
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                                        "rows": rows
                                    }
                                }
                                print(json.dumps(solution, indent=2))
                                return

if __name__ == "__main__":
    main()