from z3 import *
import json

def main():
    s = Solver()
    n = 5  # five houses, indexed 0..4 corresponding to houses 1..5

    # Create a variable for each attribute in each house.
    # Each attribute is an integer between 0 and 4.
    Names     = [Int(f"Name_{i}") for i in range(n)]
    Heights   = [Int(f"Height_{i}") for i in range(n)]
    Cigars    = [Int(f"Cigar_{i}") for i in range(n)]
    Smoothies = [Int(f"Smoothie_{i}") for i in range(n)]
    Phones    = [Int(f"Phone_{i}") for i in range(n)]

    # Domain constraints: each attribute is in 0..4.
    for i in range(n):
        s.add(And(Names[i] >= 0, Names[i] < 5))
        s.add(And(Heights[i] >= 0, Heights[i] < 5))
        s.add(And(Cigars[i] >= 0, Cigars[i] < 5))
        s.add(And(Smoothies[i] >= 0, Smoothies[i] < 5))
        s.add(And(Phones[i] >= 0, Phones[i] < 5))

    # All attributes must be distinct across houses.
    s.add(Distinct(Names))
    s.add(Distinct(Heights))
    s.add(Distinct(Cigars))
    s.add(Distinct(Smoothies))
    s.add(Distinct(Phones))

    # We use the following index-to-name mappings:
    #
    # Names:      0 = Peter,    1 = Arnold,   2 = Eric,     3 = Bob,      4 = Alice
    # Heights:    0 = average,  1 = very tall,2 = very short,3 = short,    4 = tall
    # Cigars:     0 = prince,   1 = dunhill,  2 = blends,   3 = pall mall,4 = blue master
    # Smoothies:  0 = lime,     1 = cherry,   2 = dragonfruit,3 = watermelon,4 = desert
    # Phones:     0 = oneplus 9,1 = samsung galaxy s21,2 = iphone 13,
    #             3 = huawei p50,4 = google pixel 6

    # Clue 1: The Prince smoker is the Desert smoothie lover.
    for i in range(n):
        s.add(Implies(Cigars[i] == 0, Smoothies[i] == 4))
        s.add(Implies(Smoothies[i] == 4, Cigars[i] == 0))

    # Clue 2: There is one house between Eric and Alice.
    # (Since there is exactly one house in between, the positions differ by 2.)
    s.add(Or(
        And(Names[0] == 2, Names[2] == 4),
        And(Names[0] == 4, Names[2] == 2),
        And(Names[1] == 2, Names[3] == 4),
        And(Names[1] == 4, Names[3] == 2),
        And(Names[2] == 2, Names[4] == 4),
        And(Names[2] == 4, Names[4] == 2)
    ))
    
    # Clue 3: The person who is short smokes blends.
    # (Short is Height == 3; blends is Cigar == 2.)
    for i in range(n):
        s.add(Implies(Heights[i] == 3, Cigars[i] == 2))
        s.add(Implies(Cigars[i] == 2, Heights[i] == 3))
    
    # Clue 4: The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    # (iPhone 13 means Phone == 2 and Blue Master means Cigar == 4.)
    s.add(Or(
        And(Phones[0] == 2, Cigars[1] == 4),
        And(Phones[1] == 2, Cigars[2] == 4),
        And(Phones[2] == 2, Cigars[3] == 4),
        And(Phones[3] == 2, Cigars[4] == 4)
    ))
    
    # Clue 5: The person who has an average height is the Dunhill smoker.
    # (Average height: 0; Dunhill: 1.)
    for i in range(n):
        s.add(Implies(Heights[i] == 0, Cigars[i] == 1))
        s.add(Implies(Cigars[i] == 1, Heights[i] == 0))
    
    # Clue 6: Eric is the person who is very tall.
    # (Eric is Name == 2 and very tall is Height == 1.)
    for i in range(n):
        s.add(Implies(Names[i] == 2, Heights[i] == 1))
    
    # Clue 7: Arnold is directly left of the person who uses a Huawei P50.
    # (Arnold is Name == 1; Huawei P50 is Phone == 3.)
    s.add(Or(
        And(Names[0] == 1, Phones[1] == 3),
        And(Names[1] == 1, Phones[2] == 3),
        And(Names[2] == 1, Phones[3] == 3),
        And(Names[3] == 1, Phones[4] == 3)
    ))
    
    # Clue 8: Bob is not in the fourth house.
    # (Bob is Name == 3; fourth house is index 3.)
    s.add(Names[3] != 3)
    
    # Clue 9: Eric is directly left of the person who likes Cherry smoothies.
    # (Cherry is Smoothie == 1.)
    s.add(Or(
        And(Names[0] == 2, Smoothies[1] == 1),
        And(Names[1] == 2, Smoothies[2] == 1),
        And(Names[2] == 2, Smoothies[3] == 1),
        And(Names[3] == 2, Smoothies[4] == 1)
    ))
    
    # Clue 10: Bob is the Dunhill smoker.
    for i in range(n):
        s.add(Implies(Names[i] == 3, Cigars[i] == 1))
    
    # Clue 11: The Dragonfruit smoothie lover is Bob.
    # (Dragonfruit is Smoothie == 2.)
    for i in range(n):
        s.add(Implies(Names[i] == 3, Smoothies[i] == 2))
        s.add(Implies(Smoothies[i] == 2, Names[i] == 3))
    
    # Clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    # (OnePlus 9 is Phone == 0.)
    s.add(Or(
        And(Phones[0] == 2, Phones[1] == 0), And(Phones[0] == 0, Phones[1] == 2),
        And(Phones[1] == 2, Phones[2] == 0), And(Phones[1] == 0, Phones[2] == 2),
        And(Phones[2] == 2, Phones[3] == 0), And(Phones[2] == 0, Phones[3] == 2),
        And(Phones[3] == 2, Phones[4] == 0), And(Phones[3] == 0, Phones[4] == 2)
    ))
    
    # Clue 13: The person who uses a Samsung Galaxy S21 is the person who is short.
    # (Samsung Galaxy S21 is Phone == 1; short is Height == 3.)
    for i in range(n):
        s.add(Implies(Phones[i] == 1, Heights[i] == 3))
    
    # Clue 14: There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
    # (Very tall: Height == 1; Dragonfruit: Smoothie == 2.)
    # In a row of 5 houses, possible pairs (with difference 3 in their indices) are: (0,3) and (1,4) or vice‐versa.
    s.add(Or(
        And(Heights[0] == 1, Smoothies[3] == 2),
        And(Heights[1] == 1, Smoothies[4] == 2),
        And(Heights[3] == 1, Smoothies[0] == 2),
        And(Heights[4] == 1, Smoothies[1] == 2)
    ))
    
    # Clue 15: The person who uses an iPhone 13 is Eric.
    # (iPhone 13: Phone == 2; Eric: Name == 2.)
    for i in range(n):
        s.add(Implies(Phones[i] == 2, Names[i] == 2))
    
    # Clue 16: The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    # (Desert: Smoothie == 4; Lime: Smoothie == 0.)
    # We enforce that there is at least one pair of houses with i < j 
    # such that the house at i has Desert and the house at j has Lime.
    pairs = []
    for i in range(n):
        for j in range(n):
            if i < j:
                pairs.append(And(Smoothies[i] == 4, Smoothies[j] == 0))
    s.add(Or(pairs))
    
    # Clue 17: Arnold and the person who is very short are next to each other.
    # (Arnold: Name == 1; very short: Height == 2.)
    s.add(Or(
        And(Names[0] == 1, Heights[1] == 2),
        And(Heights[0] == 2, Names[1] == 1),
        And(Names[1] == 1, Heights[2] == 2),
        And(Heights[1] == 2, Names[2] == 1),
        And(Names[2] == 1, Heights[3] == 2),
        And(Heights[2] == 2, Names[3] == 1),
        And(Names[3] == 1, Heights[4] == 2),
        And(Heights[3] == 2, Names[4] == 1)
    ))

    if s.check() == sat:
        m = s.model()
        # The mapping dictionaries to convert the model numbers back to their names.
        names_map = {0:"Peter", 1:"Arnold", 2:"Eric", 3:"Bob", 4:"Alice"}
        heights_map = {0:"average", 1:"very tall", 2:"very short", 3:"short", 4:"tall"}
        cigars_map = {0:"prince", 1:"dunhill", 2:"blends", 3:"pall mall", 4:"blue master"}
        smoothies_map = {0:"lime", 1:"cherry", 2:"dragonfruit", 3:"watermelon", 4:"desert"}
        phones_map = {0:"oneplus 9", 1:"samsung galaxy s21", 2:"iphone 13", 3:"huawei p50", 4:"google pixel 6"}

        solution_rows = []
        # Produce the solution rows in house order 1..5.
        for i in range(n):
            house_num = str(i+1)
            name_val = names_map[m.evaluate(Names[i]).as_long()]
            height_val = heights_map[m.evaluate(Heights[i]).as_long()]
            cigar_val = cigars_map[m.evaluate(Cigars[i]).as_long()]
            smoothie_val = smoothies_map[m.evaluate(Smoothies[i]).as_long()]
            phone_val = phones_map[m.evaluate(Phones[i]).as_long()]
            solution_rows.append([house_num, name_val, height_val, cigar_val, smoothie_val, phone_val])
            
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()