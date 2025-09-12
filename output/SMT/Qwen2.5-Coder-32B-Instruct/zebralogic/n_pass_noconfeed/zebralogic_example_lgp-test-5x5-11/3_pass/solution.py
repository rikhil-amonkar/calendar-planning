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
solver.add(Or([And(cigar_vars[h] == cigars.index("prince"), smoothie_vars[h] == smoothies.index("desert")) for h in houses]))

# 2. There is one house between Eric and Alice.
eric_idx = names.index("Eric")
alice_idx = names.index("Alice")
solver.add(Or(Abs(name_vars[1] - name_vars[3]) == 1,
              Abs(name_vars[2] - name_vars[4]) == 1,
              Abs(name_vars[3] - name_vars[5]) == 1))

# 3. The person who is short is the person who smokes many unique blends.
solver.add(Or([And(height_vars[h] == heights.index("short"), cigar_vars[h] == cigars.index("blends")) for h in houses]))

# 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
solver.add(Or([And(phone_vars[h] == phones.index("iphone 13"), cigar_vars[h + 1] == cigars.index("blue master")) for h in range(1, 5)]))

# 5. The person who has an average height is the Dunhill smoker.
solver.add(Or([And(height_vars[h] == heights.index("average"), cigar_vars[h] == cigars.index("dunhill")) for h in houses]))

# 6. Eric is the person who is very tall.
solver.add(Or([And(name_vars[h] == eric_idx, height_vars[h] == heights.index("very tall")) for h in houses]))

# 7. Arnold is directly left of the person who uses a Huawei P50.
arnold_idx = names.index("Arnold")
solver.add(Or([And(phone_vars[h + 1] == phones.index("huawei p50"), name_vars[h] == arnold_idx) for h in range(1, 5)]))

# 8. Bob is not in the fourth house.
bob_idx = names.index("Bob")
solver.add(name_vars[4] != bob_idx)

# 9. Eric is directly left of the person who likes Cherry smoothies.
solver.add(Or([And(smoothie_vars[h + 1] == smoothies.index("cherry"), name_vars[h] == eric_idx) for h in range(1, 5)]))

# 10. Bob is the Dunhill smoker.
solver.add(Or([And(name_vars[h] == bob_idx, cigar_vars[h] == cigars.index("dunhill")) for h in houses]))

# 11. The Dragonfruit smoothie lover is Bob.
solver.add(Or([And(smoothie_vars[h] == smoothies.index("dragonfruit"), name_vars[h] == bob_idx) for h in houses]))

# 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
solver.add(Or([Or(phone_vars[h] == phones.index("iphone 13"), phone_vars[h + 1] == phones.index("oneplus 9")) for h in range(1, 5)]))
solver.add(Or([Or(phone_vars[h] == phones.index("oneplus 9"), phone_vars[h + 1] == phones.index("iphone 13")) for h in range(1, 5)]))

# 13. The person who uses a Samsung Galaxy S21 is the person who is short.
solver.add(Or([And(phone_vars[h] == phones.index("samsung galaxy s21"), height_vars[h] == heights.index("short")) for h in houses]))

# 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
very_tall_idx = heights.index("very tall")
dragonfruit_idx = smoothies.index("dragonfruit")
solver.add(Or([Abs(h - g) == 2 for h in houses for g in houses if h != g]))

# 15. The person who uses an iPhone 13 is Eric.
solver.add(Or([And(phone_vars[h] == phones.index("iphone 13"), name_vars[h] == eric_idx) for h in houses]))

# 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
desert_idx = smoothies.index("desert")
lime_idx = smoothies.index("lime")
solver.add(Or([smoothie_vars[h] == desert_idx for h in range(1, 5)] + [smoothie_vars[h] == lime_idx for h in range(2, 6)]))

# 17. Arnold and the person who is very short are next to each other.
very_short_idx = heights.index("very short")
solver.add(Or([Abs(name_vars[h] - height_vars[h + 1]) == 1 for h in range(1, 5) if h != 5] +
              [Abs(name_vars[h + 1] - height_vars[h]) == 1 for h in range(1, 5) if h != 5]))

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