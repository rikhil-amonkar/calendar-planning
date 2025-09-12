from z3 import *

# Define the domain
houses = [1, 2, 3, 4, 5]
names = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
heights = ["average", "very tall", "very short", "short", "tall"]
cigars = ["prince", "dunhill", "blends", "pall mall", "blue master"]
smoothies = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
phones = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]

# Create variables
name_vars = {h: Int(f"name_{h}") for h in houses}
height_vars = {h: Int(f"height_{h}") for h in houses}
cigar_vars = {h: Int(f"cigar_{h}") for h in houses}
smoothie_vars = {h: Int(f"smoothie_{h}") for h in houses}
phone_vars = {h: Int(f"phone_{h}") for h in houses}

# Create solver
solver = Solver()

# Add constraints for unique values in each category
for h in houses:
    solver.add(name_vars[h] >= 0, name_vars[h] < len(names))
    solver.add(height_vars[h] >= 0, height_vars[h] < len(heights))
    solver.add(cigar_vars[h] >= 0, cigar_vars[h] < len(cigars))
    solver.add(smoothie_vars[h] >= 0, smoothie_vars[h] < len(smoothies))
    solver.add(phone_vars[h] >= 0, phone_vars[h] < len(phones))

solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([height_vars[h] for h in houses]))
solver.add(Distinct([cigar_vars[h] for h in houses]))
solver.add(Distinct([smoothie_vars[h] for h in houses]))
solver.add(Distinct([phone_vars[h] for h in houses]))

# Add clues as constraints
# 1. The Prince smoker is the Desert smoothie lover.
solver.add(And(cigar_vars[h] == cigars.index("prince"), smoothie_vars[h] == smoothies.index("desert")) for h in houses)

# 2. There is one house between Eric and Alice.
solver.add(Abs(name_vars[1] - name_vars[3]) == Abs(names.index("Eric") - names.index("Alice")) or
           Abs(name_vars[2] - name_vars[4]) == Abs(names.index("Eric") - names.index("Alice")) or
           Abs(name_vars[3] - name_vars[5]) == Abs(names.index("Eric") - names.index("Alice")))

# 3. The person who is short is the person who smokes many unique blends.
solver.add(And(height_vars[h] == heights.index("short"), cigar_vars[h] == cigars.index("blends")) for h in houses)

# 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
solver.add(phone_vars[h] == phones.index("iphone 13"), cigar_vars[h + 1] == cigars.index("blue master")) for h in range(1, 5))

# 5. The person who has an average height is the Dunhill smoker.
solver.add(And(height_vars[h] == heights.index("average"), cigar_vars[h] == cigars.index("dunhill")) for h in houses)

# 6. Eric is the person who is very tall.
solver.add(And(name_vars[h] == names.index("Eric"), height_vars[h] == heights.index("very tall")) for h in houses)

# 7. Arnold is directly left of the person who uses a Huawei P50.
solver.add(phone_vars[h + 1] == phones.index("huawei p50"), name_vars[h] == names.index("Arnold")) for h in range(1, 5))

# 8. Bob is not in the fourth house.
solver.add(name_vars[4] != names.index("Bob"))

# 9. Eric is directly left of the person who likes Cherry smoothies.
solver.add(smoothie_vars[h + 1] == smoothies.index("cherry"), name_vars[h] == names.index("Eric")) for h in range(1, 5))

# 10. Bob is the Dunhill smoker.
solver.add(And(name_vars[h] == names.index("Bob"), cigar_vars[h] == cigars.index("dunhill")) for h in houses)

# 11. The Dragonfruit smoothie lover is Bob.
solver.add(And(smoothie_vars[h] == smoothies.index("dragonfruit"), name_vars[h] == names.index("Bob")) for h in houses)

# 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
solver.add(Or(phone_vars[h] == phones.index("iphone 13"), phone_vars[h + 1] == phones.index("oneplus 9")) for h in range(1, 5))
solver.add(Or(phone_vars[h] == phones.index("oneplus 9"), phone_vars[h + 1] == phones.index("iphone 13")) for h in range(1, 5))

# 13. The person who uses a Samsung Galaxy S21 is the person who is short.
solver.add(And(phone_vars[h] == phones.index("samsung galaxy s21"), height_vars[h] == heights.index("short")) for h in houses)

# 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
solver.add(Abs(height_vars[h] - smoothie_vars[h + 3]) == Abs(heights.index("very tall") - smoothies.index("dragonfruit")) for h in range(1, 3))

# 15. The person who uses an iPhone 13 is Eric.
solver.add(And(phone_vars[h] == phones.index("iphone 13"), name_vars[h] == names.index("Eric")) for h in houses)

# 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
solver.add(Or(smoothie_vars[h] == smoothies.index("desert"), smoothie_vars[h + 1] == smoothies.index("lime")) for h in range(1, 5))

# 17. Arnold and the person who is very short are next to each other.
solver.add(Abs(name_vars[h] - height_vars[h + 1]) == Abs(names.index("Arnold") - heights.index("very short")) for h in range(1, 5))
solver.add(Abs(name_vars[h + 1] - height_vars[h]) == Abs(names.index("Arnold") - heights.index("very short")) for h in range(1, 5))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name = names[model[name_vars[h]].as_long()]
        height = heights[model[height_vars[h]].as_long()]
        cigar = cigars[model[cigar_vars[h]].as_long()]
        smoothie = smoothies[model[smoothie_vars[h]].as_long()]
        phone = phones[model[phone_vars[h]].as_long()]
        solution.append([str(h), name, height, cigar, smoothie, phone])
    
    import json
    print(json.dumps({"solution": {"header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"], "rows": solution}}))
else:
    print("No solution found")