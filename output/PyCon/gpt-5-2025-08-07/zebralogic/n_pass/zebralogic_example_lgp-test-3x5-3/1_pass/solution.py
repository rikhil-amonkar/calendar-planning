import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3]

    names = ["Eric", "Peter", "Arnold"]
    smoothies = ["cherry", "watermelon", "desert"]
    flowers = ["carnations", "lilies", "daffodils"]
    animals = ["cat", "horse", "bird"]
    hobbies = ["photography", "cooking", "gardening"]

    problem = Problem()

    # Add variables for each item in each category
    for item in names + smoothies + flowers + animals + hobbies:
        problem.addVariable(item, houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), smoothies)
    problem.addConstraint(AllDifferentConstraint(), flowers)
    problem.addConstraint(AllDifferentConstraint(), animals)
    problem.addConstraint(AllDifferentConstraint(), hobbies)

    # Clues implementation:

    # 1. The person who keeps horses and the photography enthusiast are next to each other.
    problem.addConstraint(lambda horse, photography: abs(horse - photography) == 1, ("horse", "photography"))

    # 2. The bird keeper is the person who likes Cherry smoothies.
    problem.addConstraint(lambda bird, cherry: bird == cherry, ("bird", "cherry"))

    # 3. The person who loves cooking is the Desert smoothie lover.
    problem.addConstraint(lambda cooking, desert: cooking == desert, ("cooking", "desert"))

    # 4. The person who enjoys gardening is the person who loves a carnations arrangement.
    problem.addConstraint(lambda gardening, carnations: gardening == carnations, ("gardening", "carnations"))

    # 5. The person who loves cooking is directly left of Peter.
    problem.addConstraint(lambda cooking, Peter: cooking + 1 == Peter, ("cooking", "Peter"))

    # 6. The person who loves a bouquet of daffodils is the Desert smoothie lover.
    problem.addConstraint(lambda daffodils, desert: daffodils == desert, ("daffodils", "desert"))

    # 7. The Watermelon smoothie lover is the person who keeps horses.
    problem.addConstraint(lambda watermelon, horse: watermelon == horse, ("watermelon", "horse"))

    # 8. The photography enthusiast is Eric.
    problem.addConstraint(lambda photography, Eric: photography == Eric, ("photography", "Eric"))

    solutions = problem.getSolutions()
    if not solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": []
            }
        }
        print(json.dumps(output))
        return

    # Choose a deterministic solution (in case multiple) by sorting on a fixed variable order
    var_order = names + smoothies + flowers + animals + hobbies
    solutions.sort(key=lambda s: tuple(s[v] for v in var_order))
    sol = solutions[0]

    def item_at(category, pos):
        return next(item for item in category if sol[item] == pos)

    rows = []
    for h in houses:
        row = [
            str(h),
            item_at(names, h),
            item_at(smoothies, h),
            item_at(flowers, h),
            item_at(animals, h),
            item_at(hobbies, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()