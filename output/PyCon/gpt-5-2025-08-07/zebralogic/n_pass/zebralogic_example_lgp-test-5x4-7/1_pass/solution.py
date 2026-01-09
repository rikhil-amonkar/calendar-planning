import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4, 5]

    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    animals = ["horse", "dog", "bird", "fish", "cat"]
    nationalities = ["german", "swede", "norwegian", "brit", "dane"]

    problem = Problem()

    # Add variables for each attribute value with domain 1..5
    for n in names:
        problem.addVariable(f"Name_{n}", houses)
    for s in smoothies:
        problem.addVariable(f"Smoothie_{s}", houses)
    for a in animals:
        problem.addVariable(f"Animal_{a}", houses)
    for nat in nationalities:
        problem.addVariable(f"Nat_{nat}", houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [f"Name_{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"Smoothie_{s}" for s in smoothies])
    problem.addConstraint(AllDifferentConstraint(), [f"Animal_{a}" for a in animals])
    problem.addConstraint(AllDifferentConstraint(), [f"Nat_{nat}" for nat in nationalities])

    # Clues:
    # 1. The Swedish person is directly left of the dog owner.
    problem.addConstraint(lambda swede, dog: swede + 1 == dog, ("Nat_swede", "Animal_dog"))

    # 2. There are two houses between the dog owner and the British person.
    problem.addConstraint(lambda dog, brit: abs(dog - brit) == 3, ("Animal_dog", "Nat_brit"))

    # 3. The Dane is the person who keeps horses.
    problem.addConstraint(lambda dane, horse: dane == horse, ("Nat_dane", "Animal_horse"))

    # 4. The bird keeper is somewhere to the right of the cat lover.
    problem.addConstraint(lambda bird, cat: bird > cat, ("Animal_bird", "Animal_cat"))

    # 5. The dog owner is directly left of the person who drinks Lime smoothies.
    problem.addConstraint(lambda dog, lime: dog + 1 == lime, ("Animal_dog", "Smoothie_lime"))

    # 6. Eric is the cat lover.
    problem.addConstraint(lambda eric, cat: eric == cat, ("Name_Eric", "Animal_cat"))

    # 7. Bob is the bird keeper.
    problem.addConstraint(lambda bob, bird: bob == bird, ("Name_Bob", "Animal_bird"))

    # 8. The person who likes Cherry smoothies is directly left of Peter.
    problem.addConstraint(lambda cherry, peter: cherry + 1 == peter, ("Smoothie_cherry", "Name_Peter"))

    # 9. The bird keeper is the Watermelon smoothie lover.
    problem.addConstraint(lambda bird, watermelon: bird == watermelon, ("Animal_bird", "Smoothie_watermelon"))

    # 10. The Desert smoothie lover is the dog owner.
    problem.addConstraint(lambda desert, dog: desert == dog, ("Smoothie_desert", "Animal_dog"))

    # 11. The person who keeps horses is in the third house.
    problem.addConstraint(lambda horse: horse == 3, ("Animal_horse",))

    # 12. The Norwegian is Alice.
    problem.addConstraint(lambda norwegian, alice: norwegian == alice, ("Nat_norwegian", "Name_Alice"))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found")

    sol = solutions[0]

    # Build output rows ordered by house 1..5
    rows = []
    for h in houses:
        name_at = next(n for n in names if sol[f"Name_{n}"] == h)
        smoothie_at = next(s for s in smoothies if sol[f"Smoothie_{s}"] == h)
        animal_at = next(a for a in animals if sol[f"Animal_{a}"] == h)
        nat_at = next(nat for nat in nationalities if sol[f"Nat_{nat}"] == h)
        rows.append([str(h), name_at, smoothie_at, animal_at, nat_at])

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()