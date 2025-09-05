from z3 import *
import json

def main():
    s = Solver()
    houses = 6

    # Create variables for each house: name, hair, and height.
    name = [Int("name_%d" % i) for i in range(houses)]
    hair = [Int("hair_%d" % i) for i in range(houses)]
    height = [Int("height_%d" % i) for i in range(houses)]
    
    # Each variable is in the domain 0..5.
    for i in range(houses):
        s.add(And(name[i] >= 0, name[i] < houses))
        s.add(And(hair[i] >= 0, hair[i] < houses))
        s.add(And(height[i] >= 0, height[i] < houses))
    
    # All attributes must be all different (permutations).
    s.add(Distinct(name))
    s.add(Distinct(hair))
    s.add(Distinct(height))
    
    # Mappings for readability:
    # Names: 0: Bob, 1: Peter, 2: Eric, 3: Alice, 4: Arnold, 5: Carol
    # Hair Colors: 0: auburn, 1: blonde, 2: brown, 3: black, 4: red, 5: gray
    # Heights: 0: very tall, 1: average, 2: very short, 3: tall, 4: super tall, 5: short

    # Constraint 1: The person with blonde hair is directly left of Bob.
    # Blonde hair is 1 and Bob is 0.
    for i in range(houses):
        if i < houses - 1:
            s.add(Implies(hair[i] == 1, name[i+1] == 0))
        else:
            s.add(hair[i] != 1)
    
    # Constraint 2: Alice is in the fourth house (index 3).
    # Alice is 3.
    s.add(name[3] == 3)
    
    # Constraint 3: The person who is short is Arnold.
    # "short" is 5 and Arnold is 4.
    for i in range(houses):
        s.add(Implies(name[i] == 4, height[i] == 5))
        s.add(Implies(height[i] == 5, name[i] == 4))
    
    # Constraint 4: The person who is tall is in the sixth house (index 5).
    # "tall" is 3.
    s.add(height[5] == 3)
    
    # Constraint 5: The person who has black hair is not in the fourth house (index 3).
    # "black" is 3.
    s.add(hair[3] != 3)
    
    # Constraint 6: The person who has red hair is Eric.
    # "red" is 4 and Eric is 2.
    for i in range(houses):
        s.add(Implies(hair[i] == 4, name[i] == 2))
        s.add(Implies(name[i] == 2, hair[i] == 4))
    
    # Constraint 7: The person who is super tall is somewhere to the right of the person who has an average height.
    # "average" is 1; "super tall" is 4.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(height[i] == 1, height[j] == 4), i < j))
    
    # Constraint 8: The person who has blonde hair is Carol.
    # Blonde hair is 1 and Carol is 5.
    for i in range(houses):
        s.add(Implies(hair[i] == 1, name[i] == 5))
        s.add(Implies(name[i] == 5, hair[i] == 1))
    
    # Constraint 9: There is one house between the person who has gray hair and the person who has red hair.
    # Gray hair is 5 and red hair is 4.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(hair[i] == 5, hair[j] == 4), Or(j == i + 2, j == i - 2)))
    
    # Constraint 10: The person who is very short is in the fifth house (index 4).
    # "very short" is 2.
    s.add(height[4] == 2)
    
    # Constraint 11: Bob is the person who has brown hair.
    # Bob is 0 and brown hair is 2.
    for i in range(houses):
        s.add(Implies(name[i] == 0, hair[i] == 2))
        s.add(Implies(hair[i] == 2, name[i] == 0))
    
    # Constraint 12: The person who has gray hair is in the third house (index 2).
    s.add(hair[2] == 5)
    
    # Constraint 13: The person who has blonde hair is the person who is very tall.
    # "very tall" is 0.
    for i in range(houses):
        s.add(Implies(hair[i] == 1, height[i] == 0))
        s.add(Implies(height[i] == 0, hair[i] == 1))
    
    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()
        name_list = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
        hair_list = ["auburn", "blonde", "brown", "black", "red", "gray"]
        height_list = ["very tall", "average", "very short", "tall", "super tall", "short"]
        
        # Prepare the result in the required JSON format.
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor", "Height"],
                "rows": []
            }
        }
        # Houses are numbered 1 to 6 in order.
        for i in range(houses):
            house_num = str(i + 1)
            name_val = name_list[m.evaluate(name[i]).as_long()]
            hair_val = hair_list[m.evaluate(hair[i]).as_long()]
            height_val = height_list[m.evaluate(height[i]).as_long()]
            result["solution"]["rows"].append([house_num, name_val, hair_val, height_val])
        
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()