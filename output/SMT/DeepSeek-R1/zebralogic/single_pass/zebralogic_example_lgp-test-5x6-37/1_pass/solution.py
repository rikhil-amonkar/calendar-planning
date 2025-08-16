from z3 import *
import json

def main():
    # Define the enums for each attribute
    Name, (Bob, Arnold, Alice, Peter, Eric) = EnumSort('Name', ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric'])
    Hobby, (cooking, gardening, painting, photography, knitting) = EnumSort('Hobby', ['cooking', 'gardening', 'painting', 'photography', 'knitting'])
    Sport, (swimming, tennis, soccer, baseball, basketball) = EnumSort('Sport', ['swimming', 'tennis', 'soccer', 'baseball', 'basketball'])
    Style, (ranch, craftsman, victorian, modern, colonial) = EnumSort('Style', ['ranch', 'craftsman', 'victorian', 'modern', 'colonial'])
    Child, (Timothy, Samantha, Bella, Meredith, Fred) = EnumSort('Child', ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred'])
    Height, (average, very_tall, very_short, short, tall) = EnumSort('Height', ['average', 'very tall', 'very short', 'short', 'tall'])

    # Create variables for each house (0-indexed: house1 is index0, house2 is index1, etc.)
    n = [Const(f'n_{i}', Name) for i in range(5)]
    hby = [Const(f'hby_{i}', Hobby) for i in range(5)]
    sp = [Const(f'sp_{i}', Sport) for i in range(5)]
    sty = [Const(f'sty_{i}', Style) for i in range(5)]
    ch = [Const(f'ch_{i}', Child) for i in range(5)]
    ht = [Const(f'ht_{i}', Height) for i in range(5)]

    s = Solver()

    # Each attribute must be unique per house
    s.add(Distinct(n))
    s.add(Distinct(hby))
    s.add(Distinct(sp))
    s.add(Distinct(sty))
    s.add(Distinct(ch))
    s.add(Distinct(ht))

    # Clue 2: The tall person is in the second house (house2, index1)
    s.add(ht[1] == tall)

    # Clue 3: Peter is directly left of the Victorian house
    # Clue 20: Victorian house is in the fifth house (house5, index4)
    s.add(sty[4] == victorian)
    s.add(n[3] == Peter)  # Peter is in house4 (index3)

    # Clue 4: Alice is tall -> and since tall is in house2, Alice is in house2
    s.add(n[1] == Alice)

    # Clue 5: The baseball lover is very tall
    # Clue 16: Peter is very tall -> so Peter (house4, index3) is very tall and loves baseball
    s.add(ht[3] == very_tall)
    s.add(sp[3] == baseball)

    # Clue 6: The person with child Meredith and the person with child Timothy are adjacent
    # We define adjacency: |i - j| = 1
    s.add(Or(
        And(ch[0] == Meredith, ch[1] == Timothy),
        And(ch[1] == Meredith, Or(ch[0] == Timothy, ch[2] == Timothy)),
        And(ch[2] == Meredith, Or(ch[1] == Timothy, ch[3] == Timothy)),
        And(ch[3] == Meredith, Or(ch[2] == Timothy, ch[4] == Timothy)),
        And(ch[4] == Meredith, ch[3] == Timothy),
        And(ch[0] == Timothy, ch[1] == Meredith),
        And(ch[1] == Timothy, Or(ch[0] == Meredith, ch[2] == Meredith)),
        And(ch[2] == Timothy, Or(ch[1] == Meredith, ch[3] == Meredith)),
        And(ch[3] == Timothy, Or(ch[2] == Meredith, ch[4] == Meredith)),
        And(ch[4] == Timothy, ch[3] == Meredith)
    ))

    # Clue 7: Bob has hobby painting
    s.add(Or([And(n[i] == Bob, hby[i] == painting) for i in range(5)]))

    # Clue 8: The gardener is in the second house (house2, index1)
    s.add(hby[1] == gardening)

    # Clue 9: The very short person is to the right of Eric
    # We express: there exists i, j such that n[i] = Eric, ht[j] = very_short, and i < j
    s.add(Or([And(n[i] == Eric, ht[j] == very_short, i < j) for i in range(5) for j in range(5)]))

    # Clue 10: The tennis lover has child Samantha
    s.add(Or([And(sp[i] == tennis, ch[i] == Samantha) for i in range(5)]))

    # Clue 11: The soccer lover is not in the first house (house1, index0)
    s.add(sp[0] != soccer)

    # Clue 12: The person with child Samantha lives in a modern house
    s.add(Or([And(ch[i] == Samantha, sty[i] == modern) for i in range(5)]))

    # Clue 13: The craftsman house has average height
    s.add(Or([And(sty[i] == craftsman, ht[i] == average) for i in range(5)]))

    # Clue 14: The person with child Fred lives in the Victorian house (house5, index4)
    s.add(ch[4] == Fred)

    # Clue 15: The short person loves basketball
    s.add(Or([And(ht[i] == short, sp[i] == basketball) for i in range(5)]))

    # Clue 17: The ranch house is left of the cooking hobby
    s.add(Or([And(sty[i] == ranch, hby[j] == cooking, i < j) for i in range(5) for j in range(5)]))

    # Clue 18: The knitting and gardening hobbies are adjacent
    s.add(Or(
        And(hby[0] == knitting, hby[1] == gardening),
        And(hby[1] == knitting, Or(hby[0] == gardening, hby[2] == gardening)),
        And(hby[2] == knitting, Or(hby[1] == gardening, hby[3] == gardening)),
        And(hby[3] == knitting, Or(hby[2] == gardening, hby[4] == gardening)),
        And(hby[4] == knitting, hby[3] == gardening),
        And(hby[0] == gardening, hby[1] == knitting),
        And(hby[1] == gardening, Or(hby[0] == knitting, hby[2] == knitting)),
        And(hby[2] == gardening, Or(hby[1] == knitting, hby[3] == knitting)),
        And(hby[3] == gardening, Or(hby[2] == knitting, hby[4] == knitting)),
        And(hby[4] == gardening, hby[3] == knitting)
    ))

    # Clue 19: The modern house person has cooking hobby
    s.add(Or([And(sty[i] == modern, hby[i] == cooking) for i in range(5)]))

    # Additional constraints deduced manually for efficiency
    s.add(sty[2] == modern)    # House3 is modern
    s.add(hby[0] == knitting)  # House1 has knitting hobby

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(5):
            house = str(i+1)
            name = str(m[n[i]])
            hobby = str(m[hby[i]])
            sport = str(m[sp[i]])
            style = str(m[sty[i]])
            child = str(m[ch[i]])
            height = str(m[ht[i]])
            rows.append([house, name, hobby, sport, style, child, height])
        
        solution = {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": rows
        }
        result = {"solution": solution}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()