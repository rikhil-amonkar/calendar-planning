import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 7)

    names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
    birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
    foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
    cars = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

    problem = Problem()

    # Add variables with domains
    for n in names:
        problem.addVariable(n, houses)
    for b in birthdays:
        problem.addVariable(b, houses)
    for f in foods:
        problem.addVariable(f, houses)
    for h in heights:
        problem.addVariable(h, houses)
    for c in cars:
        problem.addVariable(c, houses)

    # All-different constraints per category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), birthdays)
    problem.addConstraint(AllDifferentConstraint(), foods)
    problem.addConstraint(AllDifferentConstraint(), heights)
    problem.addConstraint(AllDifferentConstraint(), cars)

    # Constraints
    # 1. Honda Civic owner is short.
    problem.addConstraint(lambda hc, sh: hc == sh, ["honda civic", "short"])

    # 2. Ford F-150 is in the fifth house.
    problem.addConstraint(lambda x: x == 5, ["ford f150"])

    # 3. Stir fry left of Eric.
    problem.addConstraint(lambda sf, er: sf < er, ["stir fry", "Eric"])

    # 4. May left of Carol.
    problem.addConstraint(lambda may, carol: may < carol, ["may", "Carol"])

    # 5. Very short left of April.
    problem.addConstraint(lambda vs, apr: vs < apr, ["very short", "april"])

    # 6. BMW 3 Series not in the third house.
    problem.addConstraint(lambda bmw: bmw != 3, ["bmw 3 series"])

    # 7. Two houses between stir fry and pizza.
    problem.addConstraint(lambda sf, pz: abs(sf - pz) == 3, ["stir fry", "pizza"])

    # 8. Soup directly left of Eric.
    problem.addConstraint(lambda sp, er: sp + 1 == er, ["soup", "Eric"])

    # 9. Spaghetti and May are next to each other.
    problem.addConstraint(lambda spag, may: abs(spag - may) == 1, ["spaghetti", "may"])

    # 10. Alice directly left of BMW 3 Series owner.
    problem.addConstraint(lambda al, bmw: al + 1 == bmw, ["Alice", "bmw 3 series"])

    # 11. Tesla Model 3 somewhere to the left of the person who is tall.
    problem.addConstraint(lambda tes, tal: tes < tal, ["tesla model 3", "tall"])

    # 12. Very tall is the Toyota Camry owner.
    problem.addConstraint(lambda vt, camry: vt == camry, ["very tall", "toyota camry"])

    # 13. Peter directly left of pizza lover.
    problem.addConstraint(lambda pe, pz: pe + 1 == pz, ["Peter", "pizza"])

    # 14. Stew not in the third house.
    problem.addConstraint(lambda st: st != 3, ["stew"])

    # 15. One house between September and very short.
    problem.addConstraint(lambda sept, vs: abs(sept - vs) == 2, ["sept", "very short"])

    # 16. One house between March and super tall.
    problem.addConstraint(lambda mar, st: abs(mar - st) == 2, ["mar", "super tall"])

    # 17. Tall is Bob.
    problem.addConstraint(lambda tal, bob: tal == bob, ["tall", "Bob"])

    # 18. May is somewhere to the right of Alice.
    problem.addConstraint(lambda may, al: may > al, ["may", "Alice"])

    # 19. Very short is in the fourth house.
    problem.addConstraint(lambda vs: vs == 4, ["very short"])

    # 20. March is short.
    problem.addConstraint(lambda mar, sh: mar == sh, ["mar", "short"])

    # 21. Carol owns a Tesla Model 3.
    problem.addConstraint(lambda carol, tes: carol == tes, ["Carol", "tesla model 3"])

    # 22. Eric has January birthday.
    problem.addConstraint(lambda er, jan: er == jan, ["Eric", "jan"])

    solutions = problem.getSolutions()

    # Choose first solution (should be unique)
    sol = solutions[0]

    # Build output rows
    header = ["House", "Name", "Birthday", "Food", "Height", "CarModel"]

    def find_by_category(category_list, house, sol):
        for val in category_list:
            if sol[val] == house:
                return val
        return None

    rows = []
    for house in range(1, 7):
        name = find_by_category(names, house, sol)
        birthday = find_by_category(birthdays, house, sol)
        food = find_by_category(foods, house, sol)
        height = find_by_category(heights, house, sol)
        car = find_by_category(cars, house, sol)
        rows.append([str(house), name, birthday, food, height, car])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()