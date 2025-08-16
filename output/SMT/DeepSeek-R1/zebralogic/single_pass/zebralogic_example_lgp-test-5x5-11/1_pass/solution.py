from z3 import *

def main():
    # Create enums for each attribute
    Name = Datatype('Name')
    for n in ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']:
        Name.declare(n)
    Name = Name.create()

    Height = Datatype('Height')
    for h in ['average', 'very_tall', 'very_short', 'short', 'tall']:
        Height.declare(h)
    Height = Height.create()

    Cigar = Datatype('Cigar')
    for c in ['prince', 'dunhill', 'blends', 'pall_mall', 'blue_master']:
        Cigar.declare(c)
    Cigar = Cigar.create()

    Smoothie = Datatype('Smoothie')
    for s in ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']:
        Smoothie.declare(s)
    Smoothie = Smoothie.create()

    PhoneModel = Datatype('PhoneModel')
    for p in ['oneplus_9', 'samsung_galaxy_s21', 'iphone_13', 'huawei_p50', 'google_pixel_6']:
        PhoneModel.declare(p)
    PhoneModel = PhoneModel.create()

    # Create variables for each house (index 0 to 4 for house 1 to 5)
    names = [Const(f'name_{i}', Name) for i in range(5)]
    heights = [Const(f'height_{i}', Height) for i in range(5)]
    cigars = [Const(f'cigar_{i}', Cigar) for i in range(5)]
    smoothies = [Const(f'smoothie_{i}', Smoothie) for i in range(5)]
    phones = [Const(f'phone_{i}', PhoneModel) for i in range(5)]

    s = Solver()

    # All attributes must be distinct
    s.add(Distinct(names))
    s.add(Distinct(heights))
    s.add(Distinct(cigars))
    s.add(Distinct(smoothies))
    s.add(Distinct(phones))

    # Helper function to get the house index of an attribute
    def get_house_index(lst, value):
        return [If(lst[i] == value, 1, 0) for i in range(5)]

    # Clue 1: Prince smoker is Desert smoothie lover
    for i in range(5):
        s.add(Implies(cigars[i] == Cigar.prince, smoothies[i] == Smoothie.desert))

    # Clue 2: One house between Eric and Alice -> |e - a| = 2
    eric_idx = Int('eric_idx')
    alice_idx = Int('alice_idx')
    s.add(eric_idx >= 0, eric_idx < 5)
    s.add(alice_idx >= 0, alice_idx < 5)
    s.add(eric_idx != alice_idx)
    s.add(Or(eric_idx == alice_idx + 2, alice_idx == eric_idx + 2))
    for i in range(5):
        s.add(If(names[i] == Name.Eric, eric_idx == i, True))
        s.add(If(names[i] == Name.Alice, alice_idx == i, True))

    # Clue 3: Short height is Blends smoker
    for i in range(5):
        s.add(Implies(heights[i] == Height.short, cigars[i] == Cigar.blends))

    # Clue 4: iPhone 13 directly left of Blue Master smoker
    iphone_idx = Int('iphone_idx')
    blue_master_idx = Int('blue_master_idx')
    s.add(iphone_idx >= 0, iphone_idx < 5)
    s.add(blue_master_idx >= 0, blue_master_idx < 5)
    s.add(blue_master_idx == iphone_idx + 1)
    for i in range(5):
        s.add(If(phones[i] == PhoneModel.iphone_13, iphone_idx == i, True))
        s.add(If(cigars[i] == Cigar.blue_master, blue_master_idx == i, True))

    # Clue 5: Average height is Dunhill smoker
    for i in range(5):
        s.add(Implies(heights[i] == Height.average, cigars[i] == Cigar.dunhill))

    # Clue 6: Eric is very tall
    for i in range(5):
        s.add(Implies(names[i] == Name.Eric, heights[i] == Height.very_tall))

    # Clue 7: Arnold directly left of Huawei P50 user
    arnold_idx = Int('arnold_idx')
    huawei_idx = Int('huawei_idx')
    s.add(arnold_idx >= 0, arnold_idx < 5)
    s.add(huawei_idx >= 0, huawei_idx < 5)
    s.add(huawei_idx == arnold_idx + 1)
    for i in range(5):
        s.add(If(names[i] == Name.Arnold, arnold_idx == i, True))
        s.add(If(phones[i] == PhoneModel.huawei_p50, huawei_idx == i, True))

    # Clue 8: Bob is not in the fourth house (index 3)
    for i in range(5):
        if i == 3:
            s.add(names[i] != Name.Bob)

    # Clue 9: Eric directly left of Cherry smoothie lover
    cherry_idx = Int('cherry_idx')
    s.add(cherry_idx >= 0, cherry_idx < 5)
    s.add(cherry_idx == eric_idx + 1)
    for i in range(5):
        s.add(If(smoothies[i] == Smoothie.cherry, cherry_idx == i, True))

    # Clue 10: Bob is Dunhill smoker
    for i in range(5):
        s.add(Implies(names[i] == Name.Bob, cigars[i] == Cigar.dunhill))

    # Clue 11: Bob is Dragonfruit smoothie lover
    for i in range(5):
        s.add(Implies(names[i] == Name.Bob, smoothies[i] == Smoothie.dragonfruit))

    # Clue 12: iPhone 13 and OnePlus 9 are adjacent
    oneplus_idx = Int('oneplus_idx')
    s.add(oneplus_idx >= 0, oneplus_idx < 5)
    s.add(Or(iphone_idx == oneplus_idx + 1, oneplus_idx == iphone_idx + 1))
    for i in range(5):
        s.add(If(phones[i] == PhoneModel.oneplus_9, oneplus_idx == i, True))

    # Clue 13: Samsung Galaxy S21 user is short
    for i in range(5):
        s.add(Implies(phones[i] == PhoneModel.samsung_galaxy_s21, heights[i] == Height.short))

    # Clue 14: Two houses between very tall and Dragonfruit lover -> |idx_very_tall - idx_dragon| = 3
    very_tall_idx = Int('very_tall_idx')
    dragon_idx = Int('dragon_idx')
    s.add(very_tall_idx >= 0, very_tall_idx < 5)
    s.add(dragon_idx >= 0, dragon_idx < 5)
    s.add(Or(very_tall_idx == dragon_idx + 3, dragon_idx == very_tall_idx + 3))
    for i in range(5):
        s.add(If(heights[i] == Height.very_tall, very_tall_idx == i, True))
        s.add(If(smoothies[i] == Smoothie.dragonfruit, dragon_idx == i, True))

    # Clue 15: iPhone 13 user is Eric
    for i in range(5):
        s.add(Implies(phones[i] == PhoneModel.iphone_13, names[i] == Name.Eric))

    # Clue 16: Desert smoothie left of Lime smoothie
    desert_idx = Int('desert_idx')
    lime_idx = Int('lime_idx')
    s.add(desert_idx >= 0, desert_idx < 5)
    s.add(lime_idx >= 0, lime_idx < 5)
    s.add(desert_idx < lime_idx)
    for i in range(5):
        s.add(If(smoothies[i] == Smoothie.desert, desert_idx == i, True))
        s.add(If(smoothies[i] == Smoothie.lime, lime_idx == i, True))

    # Clue 17: Arnold and very short are adjacent
    very_short_idx = Int('very_short_idx')
    s.add(very_short_idx >= 0, very_short_idx < 5)
    s.add(Or(very_short_idx == arnold_idx + 1, arnold_idx == very_short_idx + 1))
    for i in range(5):
        s.add(If(heights[i] == Height.very_short, very_short_idx == i, True))

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Prepare the solution dictionary
        header = ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"]
        rows = []
        for i in range(5):
            name_val = m.evaluate(names[i])
            height_val = m.evaluate(heights[i])
            cigar_val = m.evaluate(cigars[i])
            smoothie_val = m.evaluate(smoothies[i])
            phone_val = m.evaluate(phones[i])
            # Convert Z3 datatype to string and remove any underscores for multi-word attributes
            name_str = str(name_val).replace('_', ' ')
            height_str = str(height_val).replace('_', ' ')
            cigar_str = str(cigar_val).replace('_', ' ')
            smoothie_str = str(smoothie_val)
            phone_str = str(phone_val).replace('_', ' ')
            rows.append([str(i+1), name_str, height_str, cigar_str, smoothie_str, phone_str])
        
        solution = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        # Print the solution as a JSON string (for the required format, we'll print it as a dictionary that can be serialized)
        # Since the problem requires the output to be a JSON-formatted dictionary, we return it as a Python dictionary.
        # But note: the problem says to write a Python program that outputs the code. We'll print the solution dictionary in the required structure.
        # However, the requirement is to output the JSON, but the instruction says to write the code. We are writing the code to solve and then print the JSON via the program?
        # Actually, the problem says: "Your output should be a JSON-formatted dictionary", meaning the program should output the JSON.
        # But the instruction says to write the code in the markdown. So we just build the dictionary and then print it? 
        # But the example output is a dictionary. We'll use json.dumps to output as JSON string? However, the requirement says the output must be valid JSON.
        # But note: the problem says "Write a Python program that solves it using the Z3 solver." and then output the JSON.
        # We'll output using json.dumps to ensure valid JSON.
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()