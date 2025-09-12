from z3 import *

# Define the domains
names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

# Create the solver
solver = Solver()

# Create variables
name_vars = [Int(f"name_{i+1}") for i in range(6)]
child_vars = [Int(f"child_{i+1}") for i in range(6)]
smoothie_vars = [Int(f"smoothie_{i+1}") for i in range(6)]

# Define the domains for each variable
for i in range(6):
    solver.add(name_vars[i] >= 0)
    solver.add(name_vars[i] < 6)
    solver.add(child_vars[i] >= 0)
    solver.add(child_vars[i] < 6)
    solver.add(smoothie_vars[i] >= 0)
    solver.add(smoothie_vars[i] < 6)

# All variables must be distinct
solver.add(Distinct(name_vars))
solver.add(Distinct(child_vars))
solver.add(Distinct(smoothie_vars))

# Clues implementation
# 1. The person's child is named Fred and the Desert smoothie lover are next to each other.
fred_index = children.index("Fred")
desert_index = smoothies.index("desert")
solver.add(Or(
    And(child_vars[0] == fred_index, smoothie_vars[1] == desert_index),
    And(child_vars[1] == fred_index, smoothie_vars[0] == desert_index),
    And(child_vars[1] == fred_index, smoothie_vars[2] == desert_index),
    And(child_vars[2] == fred_index, smoothie_vars[1] == desert_index),
    And(child_vars[2] == fred_index, smoothie_vars[3] == desert_index),
    And(child_vars[3] == fred_index, smoothie_vars[2] == desert_index),
    And(child_vars[3] == fred_index, smoothie_vars[4] == desert_index),
    And(child_vars[4] == fred_index, smoothie_vars[3] == desert_index),
    And(child_vars[4] == fred_index, smoothie_vars[5] == desert_index),
    And(child_vars[5] == fred_index, smoothie_vars[4] == desert_index)
))

# 2. The person who drinks Blueberry smoothies is somewhere to the left of the person's child is named Fred.
blueberry_index = smoothies.index("blueberry")
fred_var = [If(child_vars[i] == fred_index, i, 6) for i in range(6)]
blueberry_var = [If(smoothie_vars[i] == blueberry_index, i, 6) for i in range(6)]
solver.add(z3.Or([blueberry < fred for blueberry in blueberry_var for fred in fred_var if blueberry != 6 and fred != 6]))

# 3. Alice is not in the fifth house.
alice_index = names.index("Alice")
solver.add(name_vars[4] != alice_index)

# 4. The person's child is named Samantha is not in the second house.
samantha_index = children.index("Samantha")
solver.add(child_vars[1] != samantha_index)

# 5. The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
watermelon_index = smoothies.index("watermelon")
cherry_index = smoothies.index("cherry")
cherry_var = [If(smoothie_vars[i] == cherry_index, i, 6) for i in range(6)]
watermelon_var = [If(smoothie_vars[i] == watermelon_index, i, 6) for i in range(6)]
solver.add(z3.Or([cherry < watermelon for cherry in cherry_var for watermelon in watermelon_var if cherry != 6 and watermelon != 6]))

# 6. Alice is the person's child is named Alice.
solver.add(child_vars[names.index("Alice")] == children.index("Alice"))

# 7. Alice is the Watermelon smoothie lover.
solver.add(smoothie_vars[names.index("Alice")] == watermelon_index)

# 8. Peter is somewhere to the right of the person's child is named Samantha.
peter_index = names.index("Peter")
samantha_var = [If(child_vars[i] == samantha_index, i, 6) for i in range(6)]
peter_var = [If(name_vars[i] == peter_index, i, 6) for i in range(6)]
solver.add(z3.Or([samantha < peter for samantha in samantha_var for peter in peter_var if samantha != 6 and peter != 6]))

# 9. Arnold is not in the second house.
arnold_index = names.index("Arnold")
solver.add(name_vars[1] != arnold_index)

# 10. Bob is the person who is the mother of Timothy.
bob_index = names.index("Bob")
timothy_index = children.index("Timothy")
solver.add(child_vars[bob_index] == timothy_index)

# 11. Arnold is directly left of Carol.
carol_index = names.index("Carol")
solver.add(name_vars.index(arnold_index) + 1 == name_vars.index(carol_index))

# 12. The person who likes Cherry smoothies is directly left of the person's child is named Samantha.
solver.add(smoothie_vars.index(cherry_index) + 1 == child_vars.index(samantha_index))

# 13. The person's child is named Meredith is in the sixth house.
meredith_index = children.index("Meredith")
solver.add(child_vars[5] == meredith_index)

# 14. The Dragonfruit smoothie lover is the person's child is named Meredith.
dragonfruit_index = smoothies.index("dragonfruit")
solver.add(smoothie_vars[5] == dragonfruit_index)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(6):
        name = names[model.evaluate(name_vars[i]).as_long()]
        child = children[model.evaluate(child_vars[i]).as_long()]
        smoothie = smoothies[model.evaluate(smoothie_vars[i]).as_long()]
        solution.append([str(i+1), name, child, smoothie])
    
    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": solution
        }
    }))
else:
    print("No solution found")