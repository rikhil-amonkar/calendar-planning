from z3 import *
import json

def main():
    s = Solver()
    houses = 3  # Three houses: indices 0,1,2 representing House 1,2,3

    # For each house, create an integer variable for each attribute.
    # Domain for each variable is 0,1,2 meaning one of three possible unique items.
    name   = [Int("name_%d" % i) for i in range(houses)]
    smoothie = [Int("smoothie_%d" % i) for i in range(houses)]
    flower  = [Int("flower_%d" % i) for i in range(houses)]
    animal  = [Int("animal_%d" % i) for i in range(houses)]
    hobby   = [Int("hobby_%d" % i) for i in range(houses)]

    # Each variable must be in the domain {0,1,2}
    for i in range(houses):
        s.add(And(name[i]   >= 0, name[i]   <= 2))
        s.add(And(smoothie[i] >= 0, smoothie[i] <= 2))
        s.add(And(flower[i]  >= 0, flower[i]  <= 2))
        s.add(And(animal[i]  >= 0, animal[i]  <= 2))
        s.add(And(hobby[i]   >= 0, hobby[i]   <= 2))
    
    # All houses have distinct attributes for each category.
    s.add(Distinct(name[0], name[1], name[2]))
    s.add(Distinct(smoothie[0], smoothie[1], smoothie[2]))
    s.add(Distinct(flower[0], flower[1], flower[2]))
    s.add(Distinct(animal[0], animal[1], animal[2]))
    s.add(Distinct(hobby[0], hobby[1], hobby[2]))

    # Use the following mappings for clarity:
    # Names:       Eric = 0, Peter  = 1, Arnold = 2
    # Smoothies:   cherry = 0, watermelon = 1, desert = 2
    # Flowers:     carnations = 0, lilies = 1, daffodils = 2
    # Animals:     cat = 0, horse = 1, bird = 2
    # Hobbies:     photography = 0, cooking = 1, gardening = 2

    # Clue 8: The photography enthusiast is Eric.
    # Means: If a house’s hobby is photography then that house’s owner must be Eric,
    # and conversely if a house’s owner is Eric then his hobby is photography.
    for i in range(houses):
        s.add(Implies(hobby[i] == 0, name[i] == 0))
        s.add(Implies(name[i] == 0, hobby[i] == 0))

    # Clue 2: The bird keeper is the person who likes Cherry smoothies.
    for i in range(houses):
        s.add(Implies(animal[i] == 2, smoothie[i] == 0))
        s.add(Implies(smoothie[i] == 0, animal[i] == 2))

    # Clue 3: The person who loves cooking is the Desert smoothie lover.
    for i in range(houses):
        s.add(Implies(hobby[i] == 1, smoothie[i] == 2))
        s.add(Implies(smoothie[i] == 2, hobby[i] == 1))

    # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
    for i in range(houses):
        s.add(Implies(flower[i] == 2, smoothie[i] == 2))
        s.add(Implies(smoothie[i] == 2, flower[i] == 2))

    # Clue 4: The person who enjoys gardening is the person who loves carnations.
    for i in range(houses):
        s.add(Implies(hobby[i] == 2, flower[i] == 0))
        s.add(Implies(flower[i] == 0, hobby[i] == 2))

    # Clue 5: The person who loves cooking is directly left of Peter.
    # (House order: 0 (leftmost), 1, 2 (rightmost))
    for i in range(houses - 1):
        s.add(Implies(hobby[i] == 1, name[i+1] == 1))
    # Cooking cannot be in the rightmost house because there is no house to its right.
    s.add(hobby[2] != 1)

    # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
    for i in range(houses):
        s.add(Implies(smoothie[i] == 1, animal[i] == 1))
        s.add(Implies(animal[i] == 1, smoothie[i] == 1))

    # Clue 1: The person who keeps horses and the photography enthusiast (i.e. Eric) are next to each other.
    # For any house that has horses, at least one neighbor must have photography.
    for i in range(houses):
        if i == 0:
            s.add(Implies(animal[i] == 1, hobby[i+1] == 0))
        elif i == houses - 1:
            s.add(Implies(animal[i] == 1, hobby[i-1] == 0))
        else:
            s.add(Implies(animal[i] == 1, Or(hobby[i-1] == 0, hobby[i+1] == 0)))

    if s.check() == sat:
        m = s.model()
        # Reverse mappings for output
        names_map = {0: "Eric", 1: "Peter", 2: "Arnold"}
        smoothies_map = {0: "cherry", 1: "watermelon", 2: "desert"}
        flowers_map = {0: "carnations", 1: "lilies", 2: "daffodils"}
        animals_map = {0: "cat", 1: "horse", 2: "bird"}
        hobbies_map = {0: "photography", 1: "cooking", 2: "gardening"}

        solution_rows = []
        for i in range(houses):
            row = [
                str(i+1),
                names_map[m[name[i]].as_long()],
                smoothies_map[m[smoothie[i]].as_long()],
                flowers_map[m[flower[i]].as_long()],
                animals_map[m[animal[i]].as_long()],
                hobbies_map[m[hobby[i]].as_long()]
            ]
            solution_rows.append(row)

        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()