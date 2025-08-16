from z3 import *

# Define the lists for each attribute
names_list = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
vacations_list = ["cruise", "city", "camping", "beach", "mountain"]
children_list = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
nationalities_list = ["dane", "norwegian", "brit", "german", "swede"]

# Initialize solver
s = Solver()

# Create variables for each house (0-4)
names_vars = [Int('names_%d' % i) for i in range(5)]
vacations_vars = [Int('vacations_%d' % i) for i in range(5)]
children_vars = [Int('children_%d' % i) for i in range(5)]
nationalities_vars = [Int('nationalities_%d' % i) for i in range(5)]

# Add permutation constraints
for vars_list in [names_vars, vacations_vars, children_vars, nationalities_vars]:
    s.add(Distinct(vars_list))
    s.add(And([And(0 <= var, var <= 4) for var in vars_list]))

# Add clues
# Clue 1: Norwegian is Peter (names 4 → nationality 1)
for h in range(5):
    s.add(Implies(names_vars[h] == 4, nationalities_vars[h] == 1))

# Clue 2: Swede's child is Bella (nationality 4 → child 0)
for h in range(5):
    s.add(Implies(nationalities_vars[h] == 4, children_vars[h] == 0))

# Clue 3: Beach (3) left of Samantha (1)
s.add(Or([And(vacations_vars[h] == 3, children_vars[h+1] == 1) for h in range(4)]))

# Clue 4: Child Bella not in house 2 (index 1)
s.add(children_vars[1] != 0)

# Clue 5: Alice is British (name 0 → nationality 2)
for h in range(5):
    s.add(Implies(names_vars[h] == 0, nationalities_vars[h] == 2))

# Clue 6: Cruise in first house (vacations[0] = 0)
s.add(vacations_vars[0] == 0)

# Clue 7: Child Meredith (3) in house 4 (index 3)
s.add(children_vars[3] == 3)

# Clue 8: Eric not in house 5 (names[4] !=3)
s.add(names_vars[4] != 3)

# Clue 9: Swede to the right of Norwegian (Peter)
h1_9, h2_9 = Ints('h1_9 h2_9')
s.add(ForAll([h1_9, h2_9], Implies(And(nationalities_vars[h1_9] == 1, names_vars[h1_9] == 4, nationalities_vars[h2_9] == 4), h2_9 > h1_9)))

# Clue 10: Fred (child 2) and city (vacation 1) with one house between
h1_10, h2_10 = Ints('h1_10 h2_10')
s.add(ForAll([h1_10, h2_10], Implies(And(children_vars[h1_10] == 2, vacations_vars[h2_10] == 1), Abs(h1_10 - h2_10) == 2)))

# Clue 11: Bob (name 1) → camping (vacation 2)
for h in range(5):
    s.add(Implies(names_vars[h] == 1, vacations_vars[h] == 2))

# Clue 12: Dane in house 5 (nationalities[4] = 0)
s.add(nationalities_vars[4] == 0)

# Clue 13: Camping not in house 5 (vacations[4] !=2)
s.add(vacations_vars[4] != 2)

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = []
    for i in range(5):
        name_idx = model.eval(names_vars[i]).as_long()
        vacation_idx = model.eval(vacations_vars[i]).as_long()
        child_idx = model.eval(children_vars[i]).as_long()
        nationality_idx = model.eval(nationalities_vars[i]).as_long()
        solution.append([str(i+1), names_list[name_idx], vacations_list[vacation_idx], children_list[child_idx], nationalities_list[nationality_idx]])
    # Format as JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")