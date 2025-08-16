from z3 import Solver, Ints, And, Distinct, Or
import json

def solve_puzzle():
    # Houses are numbered 1 (left) to 3 (right)
    # Define variables representing the house position (1..3) of each attribute value
    Eric, Peter, Arnold = Ints('Eric Peter Arnold')
    BlueMaster, Prince, PallMall = Ints('BlueMaster Prince PallMall')
    Photography, Gardening, Cooking = Ints('Photography Gardening Cooking')
    HighSchool, Associate, Bachelor = Ints('HighSchool Associate Bachelor')
    Tea, Milk, Water = Ints('Tea Milk Water')

    all_vars = [
        Eric, Peter, Arnold,
        BlueMaster, Prince, PallMall,
        Photography, Gardening, Cooking,
        HighSchool, Associate, Bachelor,
        Tea, Milk, Water
    ]

    s = Solver()

    # Domain constraints: each attribute value is assigned to a house 1..3
    for v in all_vars:
        s.add(And(v >= 1, v <= 3))

    # Uniqueness within each category
    s.add(Distinct(Eric, Peter, Arnold))
    s.add(Distinct(BlueMaster, Prince, PallMall))
    s.add(Distinct(Photography, Gardening, Cooking))
    s.add(Distinct(HighSchool, Associate, Bachelor))
    s.add(Distinct(Tea, Milk, Water))

    # Clues:
    # 1. The person partial to Pall Mall is Peter.
    s.add(PallMall == Peter)

    # 2. The person who likes milk is directly left of the person with a high school diploma.
    s.add(Milk + 1 == HighSchool)

    # 3. Eric is the tea drinker.
    s.add(Eric == Tea)

    # 4. Arnold and the Prince smoker are next to each other.
    s.add(Or(Arnold == Prince + 1, Arnold == Prince - 1))

    # 5. The person who enjoys gardening is somewhere to the left of the Prince smoker.
    s.add(Gardening < Prince)

    # 6. The person who likes milk is the person with an associate's degree.
    s.add(Milk == Associate)

    # 7. The person with a bachelor's degree is directly left of the photography enthusiast.
    s.add(Bachelor + 1 == Photography)

    if s.check() != 1:  # sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Helper to extract positions and invert to house->label
    def positions(label_to_var):
        return {label: m[var].as_long() for label, var in label_to_var.items()}

    def invert(pos_dict):
        return {house: label for label, house in pos_dict.items()}

    # Build mappings for each category
    names_pos = positions({
        "Eric": Eric,
        "Peter": Peter,
        "Arnold": Arnold
    })
    cigars_pos = positions({
        "blue master": BlueMaster,
        "prince": Prince,
        "pall mall": PallMall
    })
    hobbies_pos = positions({
        "photography": Photography,
        "gardening": Gardening,
        "cooking": Cooking
    })
    educ_pos = positions({
        "high school": HighSchool,
        "associate": Associate,
        "bachelor": Bachelor
    })
    drinks_pos = positions({
        "tea": Tea,
        "milk": Milk,
        "water": Water
    })

    inv_names = invert(names_pos)
    inv_cigars = invert(cigars_pos)
    inv_hobbies = invert(hobbies_pos)
    inv_educ = invert(educ_pos)
    inv_drinks = invert(drinks_pos)

    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
            "rows": []
        }
    }

    for house in [1, 2, 3]:
        row = [
            str(house),
            inv_names[house],
            inv_cigars[house],
            inv_hobbies[house],
            inv_educ[house],
            inv_drinks[house]
        ]
        solution["solution"]["rows"].append(row)

    return solution

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result))