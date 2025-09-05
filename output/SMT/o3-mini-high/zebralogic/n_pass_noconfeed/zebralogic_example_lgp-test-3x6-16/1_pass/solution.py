import json
from z3 import Solver, Int, And, Distinct, Abs, sat

def main():
    s = Solver()
    
    # Define variables for each attribute, each taking a value in {1, 2, 3} representing the house number.
    # Names: 0 = Eric, 1 = Peter, 2 = Arnold (but we'll use variable names themselves)
    Eric = Int('Eric')
    Peter = Int('Peter')
    Arnold = Int('Arnold')
    
    # Drinks: mapping: tea, water, milk
    tea = Int('tea')
    water = Int('water')
    milk = Int('milk')
    
    # Nationalities: mapping: dane, brit, swede
    dane = Int('dane')
    brit = Int('brit')
    swede = Int('swede')
    
    # Education: mapping: high school, associate, bachelor
    high_school = Int('high_school')
    associate = Int('associate')
    bachelor = Int('bachelor')
    
    # House styles: mapping: victorian, colonial, ranch
    victorian = Int('victorian')
    colonial = Int('colonial')
    ranch = Int('ranch')
    
    # Smoothies: mapping: cherry, watermelon, desert
    cherry = Int('cherry')
    watermelon = Int('watermelon')
    desert = Int('desert')
    
    # List of all variables
    all_vars = [
        Eric, Peter, Arnold,
        tea, water, milk,
        dane, brit, swede,
        high_school, associate, bachelor,
        victorian, colonial, ranch,
        cherry, watermelon, desert
    ]
    
    # Each variable must be in the domain 1..3 (houses 1,2,3)
    for var in all_vars:
        s.add(And(var >= 1, var <= 3))
    
    # Each category must have all distinct house assignments
    s.add(Distinct(Eric, Peter, Arnold))
    s.add(Distinct(tea, water, milk))
    s.add(Distinct(dane, brit, swede))
    s.add(Distinct(high_school, associate, bachelor))
    s.add(Distinct(victorian, colonial, ranch))
    s.add(Distinct(cherry, watermelon, desert))
    
    # Clue 1: There is one house between Eric and the tea drinker.
    s.add(Abs(Eric - tea) == 2)
    
    # Clue 2: The person who likes milk is the person in a ranch-style home.
    s.add(milk == ranch)
    
    # Clue 3: The person with a bachelor's degree is in the second house.
    s.add(bachelor == 2)
    
    # Clue 4: The person with a high school diploma is the Dane.
    s.add(high_school == dane)
    
    # Clue 5: The Desert smoothie lover is the Swedish person.
    s.add(desert == swede)
    
    # Clue 6: The person residing in a Victorian house is not in the first house.
    s.add(victorian != 1)
    
    # Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
    s.add(cherry == colonial)
    
    # Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
    s.add(Arnold > victorian)
    
    # Clue 9: The person in a ranch-style home is the person with a high school diploma.
    s.add(ranch == high_school)
    
    # Check and compute the solution
    if s.check() == sat:
        m = s.model()
        
        # Build mapping dictionaries for each attribute category: key = house number, value = attribute string.
        names_dict = {}
        for var, name in [(Eric, "Eric"), (Peter, "Peter"), (Arnold, "Arnold")]:
            names_dict[m[var].as_long()] = name
        
        drinks_dict = {}
        for var, drink in [(tea, "tea"), (water, "water"), (milk, "milk")]:
            drinks_dict[m[var].as_long()] = drink
        
        nationality_dict = {}
        for var, nat in [(dane, "dane"), (brit, "brit"), (swede, "swede")]:
            nationality_dict[m[var].as_long()] = nat
        
        education_dict = {}
        for var, edu in [(high_school, "high school"), (associate, "associate"), (bachelor, "bachelor")]:
            education_dict[m[var].as_long()] = edu
        
        house_style_dict = {}
        for var, style in [(victorian, "victorian"), (colonial, "colonial"), (ranch, "ranch")]:
            house_style_dict[m[var].as_long()] = style
        
        smoothie_dict = {}
        for var, sm in [(cherry, "cherry"), (watermelon, "watermelon"), (desert, "desert")]:
            smoothie_dict[m[var].as_long()] = sm
        
        # Assemble the rows for houses 1, 2, 3, in order.
        rows = []
        for house in [1, 2, 3]:
            row = [
                str(house),
                names_dict.get(house, ""),
                drinks_dict.get(house, ""),
                nationality_dict.get(house, ""),
                education_dict.get(house, ""),
                house_style_dict.get(house, ""),
                smoothie_dict.get(house, "")
            ]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": rows
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()