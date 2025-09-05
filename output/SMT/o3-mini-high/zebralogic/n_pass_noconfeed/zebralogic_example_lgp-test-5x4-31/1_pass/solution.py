from z3 import *
import json

def main():
    s = Solver()
    houses = range(5)
    
    # Create variables for each house and category.
    name_vars = [Int(f"name{i}") for i in houses]
    vac_vars = [Int(f"vac{i}") for i in houses]
    child_vars = [Int(f"child{i}") for i in houses]
    nat_vars = [Int(f"nat{i}") for i in houses]

    # Each variable is in the domain 0..4.
    for i in houses:
        s.add(And(name_vars[i] >= 0, name_vars[i] <= 4))
        s.add(And(vac_vars[i] >= 0, vac_vars[i] <= 4))
        s.add(And(child_vars[i] >= 0, child_vars[i] <= 4))
        s.add(And(nat_vars[i] >= 0, nat_vars[i] <= 4))

    # All attributes must be different across houses.
    s.add(Distinct(name_vars))
    s.add(Distinct(vac_vars))
    s.add(Distinct(child_vars))
    s.add(Distinct(nat_vars))

    # Define domain mappings.
    names_list = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    vacations_list = ["cruise", "city", "camping", "beach", "mountain"]
    children_list = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    nationalities_list = ["dane", "norwegian", "brit", "german", "swede"]

    # Clue 1: The Norwegian is Peter.
    # Norwegian = 1, Peter = 4.
    for i in houses:
        s.add(Implies(nat_vars[i] == 1, name_vars[i] == 4))
        s.add(Implies(name_vars[i] == 4, nat_vars[i] == 1))

    # Clue 2: The Swedish person is the person whose child is named Bella.
    # Swedish = swede = 4, Bella = 0.
    for i in houses:
        s.add(Implies(nat_vars[i] == 4, child_vars[i] == 0))
        s.add(Implies(child_vars[i] == 0, nat_vars[i] == 4))

    # Clue 3: The person who loves beach vacations is directly left of the person whose child is named Samantha.
    # beach = 3, Samantha = 1.
    for i in range(4):  # from house 1 to 4 (index 0 to 3)
        s.add(Implies(vac_vars[i] == 3, child_vars[i+1] == 1))

    # Clue 4: The house where the child is named Bella is not the second house.
    # Second house is index 1.
    s.add(child_vars[1] != 0)

    # Clue 5: Alice is the British person.
    # Alice = 0; British (brit) = 2.
    for i in houses:
        s.add(Implies(name_vars[i] == 0, nat_vars[i] == 2))
        s.add(Implies(nat_vars[i] == 2, name_vars[i] == 0))

    # Clue 6: The person who likes going on cruises is in the first house.
    # First house is index 0; cruise = 0.
    s.add(vac_vars[0] == 0)

    # Clue 7: The house where the child is named Meredith is the fourth house.
    # Fourth house is index 3; Meredith = 3.
    s.add(child_vars[3] == 3)

    # Clue 8: Eric is not in the fifth house.
    # Eric = 3; fifth house is index 4.
    s.add(name_vars[4] != 3)

    # Clue 9: The Swedish person is somewhere to the right of the Norwegian.
    for i in houses:
        for j in houses:
            s.add(Implies(And(nat_vars[i] == 1, nat_vars[j] == 4), i < j))

    # Clue 10: There is one house between the house where the child is named Fred and the house whose vacation is city.
    # Fred = 2; city = 1.
    for i in houses:
        for j in houses:
            s.add(Implies(And(child_vars[i] == 2, vac_vars[j] == 1), Or(j - i == 2, i - j == 2)))

    # Clue 11: Bob is the person who enjoys camping trips.
    # Bob = 1; camping = 2.
    for i in houses:
        s.add(Implies(name_vars[i] == 1, vac_vars[i] == 2))
        s.add(Implies(vac_vars[i] == 2, name_vars[i] == 1))

    # Clue 12: The Dane is in the fifth house.
    # Dane = 0; fifth house is index 4.
    s.add(nat_vars[4] == 0)

    # Clue 13: The person who enjoys camping trips is not in the fifth house.
    s.add(vac_vars[4] != 2)

    # Check the solver.
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in houses:
            row = [
                str(i + 1),
                names_list[m[name_vars[i]].as_long()],
                vacations_list[m[vac_vars[i]].as_long()],
                children_list[m[child_vars[i]].as_long()],
                nationalities_list[m[nat_vars[i]].as_long()]
            ]
            rows.append(row)
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()