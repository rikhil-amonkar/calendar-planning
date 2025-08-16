from z3 import *
import json

def main():
    solver = Solver()

    # Create an integer variable for each attribute value.
    eric = Int('eric')
    peter = Int('peter')
    arnold = Int('arnold')
    tea = Int('tea')
    water = Int('water')
    milk = Int('milk')
    dane = Int('dane')
    brit = Int('brit')
    swede = Int('swede')
    high_school = Int('high_school')
    associate = Int('associate')
    bachelor = Int('bachelor')
    victorian = Int('victorian')
    colonial = Int('colonial')
    ranch = Int('ranch')
    cherry = Int('cherry')
    watermelon = Int('watermelon')
    desert = Int('desert')

    # All values represent a house number: 1, 2, or 3.
    variables = [
        eric, peter, arnold,
        tea, water, milk,
        dane, brit, swede,
        high_school, associate, bachelor,
        victorian, colonial, ranch,
        cherry, watermelon, desert
    ]
    for var in variables:
        solver.add(And(var >= 1, var <= 3))

    # In each category, each attribute must be in a unique house.
    solver.add(Distinct(eric, peter, arnold))
    solver.add(Distinct(tea, water, milk))
    solver.add(Distinct(dane, brit, swede))
    solver.add(Distinct(high_school, associate, bachelor))
    solver.add(Distinct(victorian, colonial, ranch))
    solver.add(Distinct(cherry, watermelon, desert))

    # Puzzle clues:
    # 1. There is one house between Eric and the tea drinker.
    solver.add(Or(eric == tea + 2, eric == tea - 2))
    
    # 2. The person who likes milk is the person in a ranch-style home.
    solver.add(milk == ranch)
    
    # 3. The person with a bachelor's degree is in the second house.
    solver.add(bachelor == 2)
    
    # 4. The person with a high school diploma is the Dane.
    solver.add(high_school == dane)
    
    # 5. The Desert smoothie lover is the Swedish person.
    solver.add(desert == swede)
    
    # 6. The person residing in a Victorian house is not in the first house.
    solver.add(victorian != 1)
    
    # 7. The person who likes Cherry smoothies is the person living in a colonial-style house.
    solver.add(cherry == colonial)
    
    # 8. Arnold is somewhere to the right of the person residing in a Victorian house.
    solver.add(arnold > victorian)
    
    # 9. The person in a ranch-style home is the person with a high school diploma.
    solver.add(ranch == high_school)

    # Check for a solution.
    if solver.check() == sat:
        model = solver.model()

        # Create mappings from attribute string to corresponding Z3 variable.
        names = {"Eric": eric, "Peter": peter, "Arnold": arnold}
        drinks = {"tea": tea, "water": water, "milk": milk}
        nationalities = {"dane": dane, "brit": brit, "swede": swede}
        educations = {"high school": high_school, "associate": associate, "bachelor": bachelor}
        house_styles = {"victorian": victorian, "colonial": colonial, "ranch": ranch}
        smoothies = {"cherry": cherry, "watermelon": watermelon, "desert": desert}

        # Helper function: given a house number and a mapping, return the attribute whose variable equals that house.
        def get_attribute(house, mapping):
            for attr, var in mapping.items():
                if model[var].as_long() == house:
                    return attr
            return None

        # Build the rows for houses 1 to 3.
        rows = []
        for house in [1, 2, 3]:
            row = []
            # "House" as string.
            row.append(str(house))
            row.append(get_attribute(house, names))
            row.append(get_attribute(house, drinks))
            row.append(get_attribute(house, nationalities))
            row.append(get_attribute(house, educations))
            row.append(get_attribute(house, house_styles))
            row.append(get_attribute(house, smoothies))
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()