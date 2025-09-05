import json
from z3 import Int, Solver, Distinct, And, Or, sat

def main():
    # Create Z3 integer variables for each attribute, representing the house number (1..4)
    # Names
    Peter = Int('Peter')
    Alice = Int('Alice')
    Eric = Int('Eric')
    Arnold = Int('Arnold')
    names = {
        "Peter": Peter,
        "Alice": Alice,
        "Eric": Eric,
        "Arnold": Arnold
    }

    # Hobbies
    cooking = Int('cooking')
    painting = Int('painting')
    gardening = Int('gardening')
    photography = Int('photography')
    hobbies = {
        "cooking": cooking,
        "painting": painting,
        "gardening": gardening,
        "photography": photography
    }

    # Animals
    horse = Int('horse')
    fish = Int('fish')
    cat = Int('cat')
    bird = Int('bird')
    animals = {
        "horse": horse,
        "fish": fish,
        "cat": cat,
        "bird": bird
    }

    # Book Genres
    fantasy = Int('fantasy')
    mystery = Int('mystery')
    romance = Int('romance')
    science_fiction = Int('science_fiction')
    books = {
        "fantasy": fantasy,
        "mystery": mystery,
        "romance": romance,
        "science fiction": science_fiction
    }

    # Birthdays
    april = Int('april')
    jan = Int('jan')
    sept = Int('sept')
    feb = Int('feb')
    birthdays = {
        "april": april,
        "jan": jan,
        "sept": sept,
        "feb": feb
    }

    # Music
    pop = Int('pop')
    rock = Int('rock')
    classical = Int('classical')
    jazz = Int('jazz')
    music = {
        "pop": pop,
        "rock": rock,
        "classical": classical,
        "jazz": jazz
    }

    # All variables list
    all_vars = list(names.values()) + list(hobbies.values()) + list(animals.values()) + list(books.values()) + list(birthdays.values()) + list(music.values())

    s = Solver()

    # Domain constraints: each variable is a house number 1..4
    for v in all_vars:
        s.add(And(v >= 1, v <= 4))

    # Uniqueness within categories
    s.add(Distinct(*names.values()))
    s.add(Distinct(*hobbies.values()))
    s.add(Distinct(*animals.values()))
    s.add(Distinct(*books.values()))
    s.add(Distinct(*birthdays.values()))
    s.add(Distinct(*music.values()))

    # Clues:
    # 1. The person who loves cooking is the person who loves romance books.
    s.add(cooking == romance)

    # 2. The person whose birthday is in February is the person who loves pop music.
    s.add(feb == pop)

    # 3. Eric is not in the second house.
    s.add(Eric != 2)

    # 4. The person who loves romance books is not in the fourth house.
    s.add(romance != 4)

    # 5. The person whose birthday is in February is the fish enthusiast.
    s.add(feb == fish)

    # 6. Alice is somewhere to the right of the person who loves fantasy books.
    s.add(Alice > fantasy)

    # 7. The person who keeps horses is the person who loves rock music.
    s.add(horse == rock)

    # 8. The person who enjoys gardening is the person whose birthday is in April.
    s.add(gardening == april)

    # 9. The person who loves jazz music is the person who loves cooking.
    s.add(jazz == cooking)

    # 10. The person who loves rock music is the person who loves mystery books.
    s.add(rock == mystery)

    # 11. The person who paints as a hobby is directly left of the person who loves romance books.
    s.add(painting + 1 == romance)

    # 12. Peter is the person who loves pop music.
    s.add(Peter == pop)

    # 13. The person who enjoys gardening is Arnold.
    s.add(gardening == Arnold)

    # 14. The person who loves rock music is directly left of the person whose birthday is in January.
    s.add(rock + 1 == jan)

    # 15. The person who loves cooking is not in the third house.
    s.add(cooking != 3)

    # 16. The cat lover is somewhere to the right of the person who keeps horses.
    s.add(cat > horse)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Helper to get label for the given house from a category dictionary
    def label_for_house(category_dict, house_num):
        for label, var in category_dict.items():
            if m[var].as_long() == house_num:
                return label
        return None

    # Build rows
    rows = []
    for h in range(1, 5):
        row = [
            str(h),
            label_for_house(names, h),
            label_for_house(hobbies, h),
            label_for_house(animals, h),
            label_for_house(books, h),
            label_for_house(birthdays, h),
            label_for_house(music, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()