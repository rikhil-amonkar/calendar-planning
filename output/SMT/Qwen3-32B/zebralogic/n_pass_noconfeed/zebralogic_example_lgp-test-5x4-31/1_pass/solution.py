import z3
import json

# Define EnumSorts for each category
NameEnum, (Alice, Bob, Arnold, Eric, Peter) = z3.EnumSort('NameEnum', ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter'])
VacationEnum, (cruise, city, camping, beach, mountain) = z3.EnumSort('VacationEnum', ['cruise', 'city', 'camping', 'beach', 'mountain'])
ChildrenEnum, (Bella, Samantha, Fred, Meredith, Timothy) = z3.EnumSort('ChildrenEnum', ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy'])
NationalityEnum, (dane, norwegian, brit, german, swede) = z3.EnumSort('NationalityEnum', ['dane', 'norwegian', 'brit', 'german', 'swede'])

# Create variables for each house (0-4)
n0, n1, n2, n3, n4 = z3.Consts('n0 n1 n2 n3 n4', NameEnum)
vac0, vac1, vac2, vac3, vac4 = z3.Consts('vac0 vac1 vac2 vac3 vac4', VacationEnum)
child0, child1, child2, child3, child4 = z3.Consts('child0 child1 child2 child3 child4', ChildrenEnum)
nat0, nat1, nat2, nat3, nat4 = z3.Consts('nat0 nat1 nat2 nat3 nat4', NationalityEnum)

solver = z3.Solver()

# Add distinct constraints for each category
solver.add(z3.Distinct(n0, n1, n2, n3, n4))
solver.add(z3.Distinct(vac0, vac1, vac2, vac3, vac4))
solver.add(z3.Distinct(child0, child1, child2, child3, child4))
solver.add(z3.Distinct(nat0, nat1, nat2, nat3, nat4))

# Add clues as constraints
# Clue 1: Norwegian is Peter
solver.add(
    z3.Implies(nat0 == norwegian, n0 == Peter),
    z3.Implies(nat1 == norwegian, n1 == Peter),
    z3.Implies(nat2 == norwegian, n2 == Peter),
    z3.Implies(nat3 == norwegian, n3 == Peter),
    z3.Implies(nat4 == norwegian, n4 == Peter)
)

# Clue 2: Swedish person's child is Bella
solver.add(
    z3.Implies(nat0 == swede, child0 == Bella),
    z3.Implies(nat1 == swede, child1 == Bella),
    z3.Implies(nat2 == swede, child2 == Bella),
    z3.Implies(nat3 == swede, child3 == Bella),
    z3.Implies(nat4 == swede, child4 == Bella)
)

# Clue 3: Beach directly left of Samantha's child
clue3 = z3.Or(
    z3.And(vac0 == beach, child1 == Samantha),
    z3.And(vac1 == beach, child2 == Samantha),
    z3.And(vac2 == beach, child3 == Samantha),
    z3.And(vac3 == beach, child4 == Samantha)
)
solver.add(clue3)

# Clue 4: child in house 2 (index 1) is not Bella
solver.add(child1 != Bella)

# Clue 5: Alice is the Brit
solver.add(
    z3.Implies(nat0 == brit, n0 == Alice),
    z3.Implies(nat1 == brit, n1 == Alice),
    z3.Implies(nat2 == brit, n2 == Alice),
    z3.Implies(nat3 == brit, n3 == Alice),
    z3.Implies(nat4 == brit, n4 == Alice)
)

# Clue 6: Cruise is in first house (index 0)
solver.add(vac0 == cruise)

# Clue 7: child in fourth house (index 3) is Meredith
solver.add(child3 == Meredith)

# Clue 8: Eric is not in fifth house (index 4)
solver.add(n4 != Eric)

# Clue 9: Swede is to the right of Norwegian
clue9 = z3.Or(
    z3.And(nat0 == norwegian, nat1 == swede),
    z3.And(nat0 == norwegian, nat2 == swede),
    z3.And(nat0 == norwegian, nat3 == swede),
    z3.And(nat0 == norwegian, nat4 == swede),
    z3.And(nat1 == norwegian, nat2 == swede),
    z3.And(nat1 == norwegian, nat3 == swede),
    z3.And(nat1 == norwegian, nat4 == swede),
    z3.And(nat2 == norwegian, nat3 == swede),
    z3.And(nat2 == norwegian, nat4 == swede),
    z3.And(nat3 == norwegian, nat4 == swede)
)
solver.add(clue9)

# Clue 10: Fred and city with one house between
clue10 = z3.Or(
    z3.And(child0 == Fred, vac2 == city),
    z3.And(child2 == Fred, vac0 == city),
    z3.And(child1 == Fred, vac3 == city),
    z3.And(child3 == Fred, vac1 == city),
    z3.And(child2 == Fred, vac4 == city),
    z3.And(child4 == Fred, vac2 == city)
)
solver.add(clue10)

# Clue 11: Bob's vacation is camping
solver.add(
    z3.Implies(n0 == Bob, vac0 == camping),
    z3.Implies(n1 == Bob, vac1 == camping),
    z3.Implies(n2 == Bob, vac2 == camping),
    z3.Implies(n3 == Bob, vac3 == camping),
    z3.Implies(n4 == Bob, vac4 == camping)
)

# Clue 12: Dane is in fifth house (index 4)
solver.add(nat4 == dane)

# Clue 13: Camping not in fifth house
solver.add(vac4 != camping)

if solver.check() == z3.sat:
    model = solver.model()
    names = [n0, n1, n2, n3, n4]
    vacations = [vac0, vac1, vac2, vac3, vac4]
    children_ = [child0, child1, child2, child3, child4]
    nationalities = [nat0, nat1, nat2, nat3, nat4]
    rows = []
    for i in range(5):
        house_num = i + 1
        name = model.eval(names[i]).decl().name()
        vacation = model.eval(vacations[i]).decl().name()
        child = model.eval(children_[i]).decl().name()
        nationality = model.eval(nationalities[i]).decl().name()
        rows.append([str(house_num), name, vacation, child, nationality])
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))