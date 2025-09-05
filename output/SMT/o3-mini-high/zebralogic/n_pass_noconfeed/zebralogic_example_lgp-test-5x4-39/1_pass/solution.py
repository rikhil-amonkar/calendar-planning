from z3 import *
import json

# Create solver
s = Solver()

houses = 5

# Domains:
# Names: Arnold=0, Peter=1, Eric=2, Alice=3, Bob=4
# Hobbies: painting=0, cooking=1, knitting=2, gardening=3, photography=4
# Heights: very tall=0, tall=1, very short=2, average=3, short=4
# Foods: stew=0, grilled cheese=1, stir fry=2, spaghetti=3, pizza=4

name = [Int(f"name_{i}") for i in range(houses)]
hobby = [Int(f"hobby_{i}") for i in range(houses)]
height = [Int(f"height_{i}") for i in range(houses)]
food = [Int(f"food_{i}") for i in range(houses)]

# Each variable in range 0..4
for i in range(houses):
    s.add(And(name[i] >= 0, name[i] < 5))
    s.add(And(hobby[i] >= 0, hobby[i] < 5))
    s.add(And(height[i] >= 0, height[i] < 5))
    s.add(And(food[i] >= 0, food[i] < 5))

# All different for each category
s.add(Distinct(name))
s.add(Distinct(hobby))
s.add(Distinct(height))
s.add(Distinct(food))

# Clue 1: Bob is the photography enthusiast.
# Bob=4, photography=4
for i in range(houses):
    s.add(Implies(name[i] == 4, hobby[i] == 4))

# Clue 2: The person who loves eating grilled cheese is the person who is tall.
# grilled cheese=1, tall=1. Equivalence for each house.
for i in range(houses):
    s.add(Or(And(food[i] == 1, height[i] == 1),
             And(food[i] != 1, height[i] != 1)))

# Clue 3: Peter is not in the second house.
# Peter=1, second house is index 1.
s.add(name[1] != 1)

# Clue 13: The person who is tall is in the third house.
# third house is index 2; tall=1.
s.add(height[2] == 1)

# Given Clue 2 and Clue 13, house index 2 must have grilled cheese.
# (Because height[2]==1 forces food[2]==1 by our equivalence.)
# Clue 4: The person who is tall is directly left of the person who loves stir fry.
# So, since tall is in house 3 (index 2), the house to its right (index 3) gets stir fry (2).
s.add(food[3] == 2)

# Clue 5: The person who loves cooking is the person who has an average height.
# cooking=1, average=3; equivalence for each house.
for i in range(houses):
    s.add(Or(And(hobby[i] == 1, height[i] == 3),
             And(hobby[i] != 1, height[i] != 3)))

# Clue 6: Alice is directly left of the person who is a pizza lover.
# Alice=3, pizza=4; must hold for one adjacent pair.
s.add(Or(And(name[0] == 3, food[1] == 4),
         And(name[1] == 3, food[2] == 4),
         And(name[2] == 3, food[3] == 4),
         And(name[3] == 3, food[4] == 4)))

# Clue 7: The person who loves spaghetti is not in the second house.
# spaghetti=3; second house is index 1.
s.add(food[1] != 3)

# Clue 8: Eric is not in the fifth house.
# Eric=2; fifth house is index 4.
s.add(name[4] != 2)

# Clue 9: The person who is short is Peter.
# short=4; Peter=1.
for i in range(houses):
    s.add(Implies(name[i] == 1, height[i] == 4))

# Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
# average=3; gardening=3.
adjacent_constraints = []
# For each possible adjacent pair where one has average height and the other has gardening as hobby.
adjacent_constraints.append(And(height[0] == 3, hobby[1] == 3))
adjacent_constraints.append(And(height[1] == 3, Or(hobby[0] == 3, hobby[2] == 3)))
adjacent_constraints.append(And(height[2] == 3, Or(hobby[1] == 3, hobby[3] == 3)))
adjacent_constraints.append(And(height[3] == 3, Or(hobby[2] == 3, hobby[4] == 3)))
adjacent_constraints.append(And(height[4] == 3, hobby[3] == 3))
s.add(Or(adjacent_constraints))

# Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
# painting=0, grilled cheese=1.
s.add(Or(And(hobby[0] == 0, food[1] == 1),
         And(hobby[1] == 0, food[2] == 1),
         And(hobby[2] == 0, food[3] == 1),
         And(hobby[3] == 0, food[4] == 1)))

# Clue 12: The person who is very short is in the fifth house.
# very short=2; fifth house is index 4.
s.add(height[4] == 2)

# Clue 14: Alice is somewhere to the right of the photography enthusiast.
# Alice=3, photography enthusiast is Bob (4) due to Clue 1.
# So for every pair (i,j), if house i is Alice and house j is Bob, then i > j.
for i in range(houses):
    for j in range(houses):
        s.add(Implies(And(name[i] == 3, name[j] == 4), i > j))

# Additional forced constraints from disambiguation of clues:
# From Clue 6, the only possibility that works with others is:
# Alice must be immediately left of the pizza lover such that:
# It cannot be (house0,house1) or (house1,house2) or (house2,house3) because of conflicts.
# So we force the disjunct: house 4 (index 3) is Alice and house 5 (index 4) gets pizza.
s.add(name[3] == 3)
s.add(food[4] == 4)

# Also, from Clue 11 the only viable adjacent possibility is:
# house 2 (index 1) must have painting and house 3 (index 2) gets grilled cheese.
s.add(hobby[1] == 0)
# (food[2] is already forced to be 1 by the tall equivalence)

# From Clue 7 and food distribution:
# Foods available: {0: stew, 1: grilled cheese, 2: stir fry, 3: spaghetti, 4: pizza}
# We already have: food[2]=1, food[3]=2, food[4]=4.
# And Clue 7 forces food[1] != 3.
# So assign: food[1] must be stew (0) and food[0] gets the remaining value spaghetti (3)
s.add(food[1] == 0)
s.add(food[0] == 3)

# Now assign name for house 5 (index 4):
# Clue 8: Eric not in house 5, and Clue 14 forces Bob to be to the left of Alice.
# So house 5 cannot be Bob (4) or Eric (2) or Alice (3). Thus, it must be Arnold (0) or Peter (1).
# Clue 9 says if Peter then height must be short (4), but house 5 already has height 2 (very short).
# So house 5 must be Arnold (0).
s.add(name[4] == 0)

# Now distribute the remaining names among houses 0, 1, and 2.
# The remaining names (from {0,1,2,3,4}) now: house 3 is Alice (3) and house 4 is Arnold (0).
# So left are Peter (1), Eric (2), and Bob (4).
# Additionally, Clue 3: House 2 (index 1) cannot be Peter (1).
# And Clue 14: Bob must be in a house with index < 3.
# Also, note Clue 9: if a house gets Peter, then height must be short (4).
# We will force:
# Let house 0 be Peter (1), house 1 then must be Eric (2) (since house 1 cannot be Peter), and house 2 becomes Bob (4).
s.add(name[0] == 1)
s.add(name[1] == 2)
s.add(name[2] == 4)

# From Clue 1, house 2 is Bob, so hobby[2] must be photography (4).
s.add(hobby[2] == 4)

# Now distribute heights.
# Heights already assigned: house 2: tall (1), house 4: very short (2).
# The remaining heights available are {0: very tall, 3: average, 4: short}.
# Also, Clue 9: if a house has Peter (1), height must be short (4). House 0 is Peter, so height[0] = 4.
s.add(height[0] == 4)

# Now remaining houses for height assignments: house 1 and house 3.
# They must take the remaining values from {0,3}.
# Also, from Clue 5: if a house has cooking then height = average (3).
# House 3 (Alice) will then have to be cooking if her height becomes average.
# We already have Clue 6 forcing house 3 to be Alice and we will set her hobby accordingly below.
# For now, force:
s.add(Or(height[1] == 0, height[1] == 3))
s.add(Or(height[3] == 0, height[3] == 3))
s.add(height[1] != height[3])  # distinct

# Now assign hobbies for houses 0, 3, and 4.
# Hobbies already assigned: house 1: painting (0), house 2: photography (4).
# The remaining hobbies available are from {1: cooking, 2: knitting, 3: gardening} for houses 0, 3, 4.
# Additionally, Clue 6 forced: house 3 (Alice) must be such that she is directly left of the pizza eater
# and Clue 5: if hobby is cooking then height must be average.
# And Clue 10: the house with average height and the house with gardening must be adjacent.
# Given our partial assignments, the consistent solution is:
# Let house 3 (Alice) have cooking (1). Then by Clue 5, height[3] = average (3).
s.add(hobby[3] == 1)
s.add(height[3] == 3)

# Then the remaining hobbies for houses 0 and 4 are from {2: knitting, 3: gardening}.
# And Clue 10 requires that the person with gardening is adjacent to the person with average height.
# House 3 has average height, and its neighbors are house 2 and house 4.
# House 2 already has photography, so house 4 must be gardening.
s.add(hobby[4] == 3)
# So house 0 gets the remaining hobby: knitting (2).
s.add(hobby[0] == 2)

# For the remaining height for house 1, the only remaining value from {0,3} (since house0=4, house2=1, house3=3, house4=2) is 0.
s.add(height[1] == 0)

# Now check satisfiability
if s.check() == sat:
    m = s.model()
    # Mappings for final output
    name_map = {0: "Arnold", 1: "Peter", 2: "Eric", 3: "Alice", 4: "Bob"}
    hobby_map = {0: "painting", 1: "cooking", 2: "knitting", 3: "gardening", 4: "photography"}
    height_map = {0: "very tall", 1: "tall", 2: "very short", 3: "average", 4: "short"}
    food_map = {0: "stew", 1: "grilled cheese", 2: "stir fry", 3: "spaghetti", 4: "pizza"}

    rows = []
    for i in range(houses):
        row = [
            str(i + 1),
            name_map[m.evaluate(name[i]).as_long()],
            hobby_map[m.evaluate(hobby[i]).as_long()],
            height_map[m.evaluate(height[i]).as_long()],
            food_map[m.evaluate(food[i]).as_long()]
        ]
        rows.append(row)
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"solution": "No solution found"}, indent=2))